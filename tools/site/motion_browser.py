# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""The browser checks of motions shown in the pages of a site built with the Verso adapters (one
of PILean's site checks, `tools/site/`):

    python3 tools/site/motion_browser.py SITE_DIR --expect DIR [--shots DIR]

SITE_DIR is the generator's `html-multi` folder; every page with a motion (`data-bp-motion`) is
checked. DIR holds the expectations of every motion shown, `<file>.json` for the animated SVG
`<file>.svg` of each rendition (`<decl>.json`, `<decl>-narrow.json`), in the form PILean's tests
write them (`PILeanTest.MotionChecks.expectations`, `PILeanTest.MotionPanelsChecks.expectations`);
a motion without its expectations fails. The site is served on 127.0.0.1 under a strict content
policy (`site_browser.serve`) and checked in Chromium (Playwright, nothing installed or
downloaded). `motion_checks` checks one page; on a Blueprint site (a caption with the switch's link)
also the switch and the link. Checked:

* with the clock paused and set, every actor of the page's moving picture is where its key still
  has it at every rest (0.05 px), on its circle at a quarter, a half and three quarters of every
  turn (0.05 px, a true arc) at the eased angle (0.5 degrees), every label and marker upright
  (0.01 degrees), and every panel of a picture of panels in phase with the others (0.05 px); this
  covers the actors' anchors and the upright marks, not every pixel (`tools/motion-browser-check.py`
  compares pixels);
* every moving picture plays on its own clock; the wide rendition is shown at 1440 px and the
  narrow one at 360 px, the other hidden and taking no space;
* switching the theme while the picture moves recolours it, and it keeps moving;
* each way of turning motion off (the system's reduced motion, `data-motion="reduce"` on the root,
  the Blueprint's switch, print media, a printed PDF) hides the moving picture and shows the stills
  with their captions; hovering, keyboard focus, a click and a tap show the poster key's still
  (exactly one picture, the poster key's file in the page's theme, filling the picture's own box,
  nothing around it moving) while the moving picture's text alternative stays in the
  accessibility tree, in both themes, and the focused picture has a ring of at least 3:1 against
  the page; after each of them ends the moving picture follows its clock again without being
  sought (the regression test for a picture frozen after it was hidden; the check is shown to
  notice a picture hidden with `display: none`);
* the captions are in the accessibility tree while the stills are hidden, and nothing is
  announced (no live region changes);
* every id of the page once, and no `data-pilean-actor` in two pictures;
* the caption's hint about pausing, shown only while motion is on; on a Blueprint site the
  caption's link leads to the motion switch;
* no content-policy report about a figure and no console error.
"""

import base64
import json
import math
import os
import re
import sys

REST_TOL = 0.05
RADIUS_TOL = 0.05
ANGLE_TOL = 0.5
UPRIGHT_TOL = 0.01

READ = """async ([sid, t]) => {
  const svg = document.getElementById(sid);
  if (t !== null) svg.setCurrentTime(t);
  await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
  const inv = svg.getScreenCTM().inverse();
  const pre = sid + '-';
  const at = (m, x, y) => [m.a * x + m.c * y + m.e, m.b * x + m.d * y + m.f];
  const actors = [], uprights = [];
  for (const g of svg.querySelectorAll('[data-pilean-actor]')) {
    const [x, y] = g.getAttribute('data-pilean-anchor').split(' ').map(Number);
    const id = g.getAttribute('data-pilean-actor');
    actors.push([id.startsWith(pre) ? id.slice(pre.length) : '?' + id,
                 at(inv.multiply(g.getScreenCTM()), x, y)]);
  }
  for (const g of svg.querySelectorAll('[data-pilean-upright]')) {
    const [x, y] = g.getAttribute('data-pilean-upright').split(' ').map(Number);
    const m = inv.multiply(g.getScreenCTM());
    uprights.push([Math.atan2(m.b, m.a) * 180 / Math.PI, at(m, x, y)]);
  }
  return {time: svg.getCurrentTime(), actors, uprights};
}"""

PIXELS = """async ([a, b]) => {
  const load = src => new Promise((ok, bad) => {
    const i = new Image(); i.onload = () => ok(i); i.onerror = bad; i.src = src; });
  const [x, y] = await Promise.all([load(a), load(b)]);
  const w = Math.min(x.width, y.width), h = Math.min(x.height, y.height);
  const grab = i => {
    const c = document.createElement('canvas'); c.width = w; c.height = h;
    const g = c.getContext('2d'); g.drawImage(i, 0, 0, w, h);
    return g.getImageData(0, 0, w, h).data; };
  const p = grab(x), q = grab(y);
  let n = 0;
  for (let k = 0; k < p.length; k += 4) {
    const d = Math.abs(p[k] - q[k]) + Math.abs(p[k + 1] - q[k + 1]) + Math.abs(p[k + 2] - q[k + 2]);
    if (d > 60) n++;
  }
  return n;
}"""

STATE = """(sid) => {
  const svg = document.getElementById(sid);
  const m = svg.closest('.pilean-motion');
  const stage = m.querySelector('.pilean-motion-stage');
  const keys = m.querySelector('.pilean-motion-keys');
  const still = m.querySelector('.pilean-motion-still');
  const box = e => { const r = e.getBoundingClientRect();
    return [Math.round(r.x * 10) / 10, Math.round(r.y * 10) / 10,
            Math.round(r.width * 10) / 10, Math.round(r.height * 10) / 10]; };
  const imgs = keys ? [...keys.querySelectorAll('img')].filter(i => i.offsetParent !== null) : [];
  const stills = [...still.querySelectorAll('img')].filter(i =>
    i.getClientRects().length && i.getBoundingClientRect().width > 0)
    .map(i => [i.currentSrc || i.src, box(i)]);
  const cs = getComputedStyle(stage);
  let bg = 'rgba(0, 0, 0, 0)';
  for (let e = stage; e && bg === 'rgba(0, 0, 0, 0)'; e = e.parentElement)
    bg = getComputedStyle(e).backgroundColor;
  const hint = m.closest('figure, .pilean-figure-page');
  const h = hint && hint.querySelector('.pilean-motion-hint');
  return {live: getComputedStyle(svg).visibility, liveOpacity: getComputedStyle(svg).opacity,
          stage: cs.visibility, stageDisplay: cs.display, stagePosition: cs.position,
          still: getComputedStyle(still).opacity, stills, stageBox: box(stage),
          keys: keys ? keys.getBoundingClientRect().height : 0,
          keysDisplay: keys ? getComputedStyle(keys).display : 'none',
          shownStills: imgs.length,
          loaded: imgs.every(i => i.complete && i.naturalWidth > 0),
          figure: (m.closest('figure') || m).getBoundingClientRect().height,
          ring: [cs.outlineStyle, cs.outlineWidth, cs.outlineColor, bg],
          hint: h ? h.offsetParent !== null : null,
          focused: document.activeElement === stage};
}"""


def console_error(m):
    """Whether a console message is an error of the page, other than the content policy's report
    of the inline event handler of Verso's table of contents (outside every figure; the policy
    reports of figures are checked by `figure_reports`)."""
    return m.type == "error" and "inline event handler" not in m.text


def uri(data):
    return "data:image/png;base64," + base64.b64encode(data).decode()


def wrap(deg):
    return (deg + 180) % 360 - 180


def first(actors, ident):
    for name, xy in actors:
        if name == ident:
            return xy
    return None


def motion_ids(page):
    """The ids of the wide moving pictures of the page, in order."""
    return page.evaluate("""() => [...document.querySelectorAll('.pilean-motion')]
      .map(m => m.querySelector('svg.pilean-motion-wide').id)""")


def file_of(page, sid):
    """The declaration a moving picture is the body of, from its file's name, with `-narrow`."""
    path = page.evaluate("(sid) => document.getElementById(sid).getAttribute('data-pilean-file')",
                         sid)
    return os.path.basename(path)[:-len(".svg")]


def position_checks(c, page, sid, spec, label):
    """Rests, arcs, uprights and phase of one moving picture against the expectations."""
    page.evaluate("(sid) => document.getElementById(sid).pauseAnimations()", sid)
    rest_err = radius_err = angle_err = upright = 0.0
    missing = []
    counts = set()
    for rest in spec["rests"]:
        seen = page.evaluate(READ, [sid, rest["t"]])
        counts.add(len(seen["uprights"]))
        upright = max([upright] + [abs(a) for a, _ in seen["uprights"]])
        if len(seen["uprights"]) == len(rest["uprights"]):
            for (_, xy), want in zip(seen["uprights"], rest["uprights"]):
                rest_err = max(rest_err, math.dist(xy, want))
        for a in rest["actors"]:
            xy = first(seen["actors"], a["id"])
            if xy is None:
                missing.append(a["id"])
                continue
            rest_err = max(rest_err, math.dist(xy, a["at"]))
    for turn in spec["turns"]:
        cc, s = turn["centre"], turn["start"]
        r = math.dist(s, cc)
        a0 = math.degrees(math.atan2(s[1] - cc[1], s[0] - cc[0]))
        for sample in turn["samples"]:
            seen = page.evaluate(READ, [sid, sample["t"]])
            upright = max([upright] + [abs(a) for a, _ in seen["uprights"]])
            xy = first(seen["actors"], turn["id"])
            if xy is None:
                missing.append(turn["id"])
                continue
            radius_err = max(radius_err, abs(math.dist(xy, cc) - r))
            if r >= 1:
                a = math.degrees(math.atan2(xy[1] - cc[1], xy[0] - cc[0]))
                angle_err = max(angle_err, abs(wrap((a - a0) - turn["sweep"] * sample["f"])))
    c.check(f"{label}: at every rest each actor and upright mark is where the key still has it",
            not missing and rest_err <= REST_TOL and counts == {spec["uprights"]},
            f"{rest_err:.3g} px, missing {missing[:3]}, uprights {counts}")
    c.check(f"{label}: every turn is a true arc at the eased angle",
            bool(spec["turns"]) and radius_err <= RADIUS_TOL and angle_err <= ANGLE_TOL,
            f"{radius_err:.3g} px, {angle_err:.3g} deg over {len(spec['turns'])} turns")
    c.check(f"{label}: labels and markers stay upright", upright <= UPRIGHT_TOL, f"{upright:.3g}")
    if spec.get("phase"):
        err, bad = 0.0, 0
        for sample in spec["phase"]:
            seen = page.evaluate(READ, [sid, sample["t"]])
            if [i for i, _ in seen["actors"]] != [i for i, _ in sample["actors"]]:
                bad += 1
                continue
            for (_, xy), (_, want) in zip(seen["actors"], sample["actors"]):
                err = max(err, math.dist(xy, want))
        c.check(f"{label}: the panels are in phase", bad == 0 and err <= REST_TOL,
                f"{err:.3g} px, {bad} times with other actors")
    page.evaluate("(sid) => document.getElementById(sid).unpauseAnimations()", sid)


def shot(page, sid):
    box = page.evaluate("""(sid) => { const r = document.getElementById(sid)
      .getBoundingClientRect(); return [r.x + scrollX, r.y + scrollY, r.width, r.height]; }""",
                        sid)
    return page.screenshot(full_page=True, clip={"x": box[0], "y": box[1], "width": box[2],
                                                 "height": box[3]})


def follows_clock(page, sid, hidden_at, cmp):
    """Whether the moving picture, shown again, draws the time of its running clock: paused
    without seeking, its picture matches the picture of that time (sought) better than half as
    well as the picture of the time it was hidden, which a frozen picture matches. Returns the
    verdict and the numbers; `None` as verdict when the two times draw the same picture. The
    pictures are compared in `cmp`, a blank page of its own (the site's policy loads no `data:`
    image)."""
    page.wait_for_timeout(400)
    page.evaluate("(sid) => document.getElementById(sid).pauseAnimations()", sid)
    page.wait_for_timeout(120)
    drawn = shot(page, sid)
    now = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)

    def at(t):
        page.evaluate("([sid, t]) => document.getElementById(sid).setCurrentTime(t)", [sid, t])
        page.wait_for_timeout(80)
        return shot(page, sid)
    best = None
    for k in range(9):
        n = cmp.evaluate(PIXELS, [uri(drawn), uri(at(now - 0.04 + 0.01 * k))])
        best = n if best is None else min(best, n)
    then = at(hidden_at)
    frozen = cmp.evaluate(PIXELS, [uri(drawn), uri(then)])
    apart = cmp.evaluate(PIXELS, [uri(at(now)), uri(then)])
    page.evaluate("(sid) => document.getElementById(sid).unpauseAnimations()", sid)
    if apart == 0:
        return None, (best, frozen, apart)
    return best == 0 or best * 2 < frozen, (best, frozen, apart)


def luminance(rgb):
    """The relative luminance of a CSS colour `rgb(r, g, b)` (WCAG 2)."""
    vals = [float(v) / 255 for v in rgb[rgb.index("(") + 1:rgb.index(")")].split(",")[:3]]
    lin = [v / 12.92 if v <= 0.04045 else ((v + 0.055) / 1.055) ** 2.4 for v in vals]
    return 0.2126 * lin[0] + 0.7152 * lin[1] + 0.0722 * lin[2]


def contrast(a, b):
    la, lb = sorted([luminance(a), luminance(b)], reverse=True)
    return (la + 0.05) / (lb + 0.05)


def page_background(page):
    """The page's background colour (the root's, else the body's, else white)."""
    return page.evaluate("""() => { for (const e of [document.body, document.documentElement]) {
      const c = getComputedStyle(e).backgroundColor; if (c !== 'rgba(0, 0, 0, 0)') return c; }
      return 'rgb(255, 255, 255)'; }""")


def poster_files(page, sid):
    """The files the still over the moving picture `sid` must show: the poster key's still of the
    rendition shown, light and dark."""
    path, poster = page.evaluate("""(sid) => { const s = document.getElementById(sid);
      return [s.getAttribute('data-pilean-file'), s.getAttribute('data-pilean-poster')]; }""", sid)
    stem = path[:-len(".svg")]
    return f"{stem}-key-{poster}.svg", f"{stem}-key-{poster}-dark.svg"


def still_problem(page, sid, during, dark):
    """None if the still shown over the moving picture is one picture, the poster key's file in
    the page's theme, filling the stage's box; else why not."""
    if len(during["stills"]) != 1:
        return f"{len(during['stills'])} still pictures have a box"
    src, box = during["stills"][0]
    light_file, dark_file = poster_files(page, sid)
    has_dark = page.evaluate("""(sid) => !!document.getElementById(sid).closest('.pilean-motion')
      .querySelector('.pilean-motion-still picture.pilean-figure-dark')""", sid)
    want = dark_file if dark and has_dark else light_file
    if not src.endswith(want.split("/")[-1]):
        return f"it shows {src}, not {want}"
    if any(abs(a - b) > 1 for a, b in zip(box, during["stageBox"])):
        return f"its box {box} is not the stage's {during['stageBox']}"
    return None


def enter(page, state, stage, sid):
    if state == "reduced motion":
        page.emulate_media(reduced_motion="reduce")
    elif state == "data-motion":
        page.evaluate("document.documentElement.setAttribute('data-motion', 'reduce')")
    elif state == "switch":
        page.locator("#bp-motion button[data-motion-choice=off]").click()
        page.locator(f"[id='{sid}']").scroll_into_view_if_needed()
    elif state == "print":
        page.emulate_media(media="print")
    elif state == "pdf":
        page.pdf(path=os.devnull)
    elif state == "hover":
        stage.hover()
    elif state == "keyboard focus":
        # the stage is a tab stop: Tab from the elements before it reaches it
        for _ in range(400):
            page.keyboard.press("Tab")
            if stage.evaluate("e => document.activeElement === e"):
                break
    elif state == "click":
        stage.click()
    elif state == "tap":
        stage.tap()


def leave(page, state):
    if state == "reduced motion":
        page.emulate_media(reduced_motion="no-preference")
    elif state == "data-motion":
        page.evaluate("document.documentElement.removeAttribute('data-motion')")
    elif state == "switch":
        page.locator("#bp-motion button[data-motion-choice=on]").click()
    elif state == "print":
        page.emulate_media(media="screen")
    elif state == "hover":
        page.mouse.move(2, 2)
    elif state in ("keyboard focus", "click", "tap"):
        page.evaluate("document.activeElement.blur()")
        page.mouse.move(2, 2)


OFF = ("reduced motion", "data-motion", "switch", "print")


FREEZE_FIXTURE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures",
                              "freeze.html")


def freeze_control(c, browser):
    """The freeze check must notice a picture hidden with `display: none`: on the fixture
    `fixtures/freeze.html` (one rotation in one segment of 8 seconds, hidden with `display: none`
    under `data-motion="reduce"`), hidden for 1.2 seconds and shown again, it must find the
    picture frozen, on each of three runs. Chromium leaves a picture whose transform is animated
    frozen until the animation repeats when it is shown again after `display: none` (the
    rotation of the fixture, every time); an animation of `opacity` mostly is not (once in eight
    runs), and a picture that draws the same at the two times (a rest that spans both) shows
    nothing either, which is why the real check retries with longer holds and the control uses a
    picture that moves all the time."""
    cmp = browser.new_page()
    verdicts = []
    for run in range(3):
        page = browser.new_page(viewport={"width": 240, "height": 240})
        page.goto("file://" + FREEZE_FIXTURE)
        page.wait_for_timeout(600 + 200 * run)
        hidden_at = page.evaluate("document.getElementById('fixture-mw').getCurrentTime()")
        page.evaluate("document.documentElement.setAttribute('data-motion', 'reduce')")
        page.wait_for_timeout(1200)
        page.evaluate("document.documentElement.removeAttribute('data-motion')")
        verdict, numbers = follows_clock(page, "fixture-mw", hidden_at, cmp)
        verdicts.append((verdict, numbers))
        page.close()
    cmp.close()
    c.check("the freeze check notices a picture hidden with display: none and shown again "
            "(a fixture, three runs)", all(v is False for v, _ in verdicts), str(verdicts))


def state_checks(c, browser, base, url, sid, label, helpers, blueprint):
    """Each way of turning motion off, and hover and focus, on the moving picture `sid`: what is
    shown, and that the picture follows its clock afterwards."""
    new_page, goto = helpers["new_page"], helpers["goto"]
    states = list(OFF[:2]) + (["switch"] if blueprint else []) + \
        ["print", "pdf", "hover", "keyboard focus", "click", "tap"]
    cmp = browser.new_page()
    for state in states:
        kw = {"viewport": {"width": 1440, "height": 900}}
        if state == "tap":
            kw["has_touch"] = True
        ctx, page = new_page(browser, **kw)
        errors = []
        page.on("console", lambda m: errors.append(m.text) if console_error(m) else None)
        goto(page, base + url)
        page.locator(f"[id='{sid}']").scroll_into_view_if_needed()
        page.wait_for_timeout(300)
        before = page.evaluate(STATE, sid)
        verdict = None
        stage = page.locator(f"[id='{sid}']").locator("xpath=ancestor::div[1]")
        for hold in (1300, 2100, 3700):
            hidden_at = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()",
                                      sid)
            enter(page, state, stage, sid)
            page.wait_for_timeout(hold)
            during = page.evaluate(STATE, sid)
            snap = page.locator(f"[id='{sid}']").locator("xpath=ancestor::div[2]").aria_snapshot()
            bg = page_background(page)
            leave(page, state)
            after = page.evaluate(STATE, sid)
            verdict, numbers = follows_clock(page, sid, hidden_at, cmp)
            if verdict is not None:
                break
        bare = page.evaluate("(sid) => document.getElementById(sid).closest('.pilean-motion')"
                             ".classList.contains('pilean-motion-bare')", sid)
        if state in OFF and bare:
            shown = during["liveOpacity"] == "0" and during["live"] == "visible" and \
                during["still"] == "1" and during["stageDisplay"] != "none" and \
                still_problem(page, sid, during, False) is None
            what = "shows the poster's still over the moving picture (the page lists the stills)"
            c.check(f"{label}: {state} {what}", shown, f"during: {during}")
        elif state in OFF:
            shown = during["live"] == "hidden" and during["stage"] == "hidden" and \
                during["stagePosition"] == "absolute" and during["stageDisplay"] != "none" and \
                during["keysDisplay"] == "grid" and during["keys"] > 20 and \
                during["shownStills"] > 0 and during["loaded"] and during["hint"] is not True
            what = "hides the moving picture (by visibility) and shows the stills, captioned"
            c.check(f"{label}: {state} {what}", shown, f"during: {during}")
        elif state == "pdf":
            c.check(f"{label}: printing a PDF leaves the picture shown on screen",
                    during["live"] == "visible", str(during))
        else:
            replaced = during["liveOpacity"] == "0" and during["live"] == "visible" and \
                during["still"] == "1" and abs(during["figure"] - before["figure"]) < 0.5 and \
                during["stageBox"][2:] == before["stageBox"][2:]
            why = still_problem(page, sid, during, False) or \
                (None if replaced else "the picture was not replaced by the still in its box")
            c.check(f"{label}: {state} shows the poster key's still in the picture's own box",
                    why is None, f"{why}: during {during}")
            alt = page.evaluate("(sid) => document.getElementById(sid).getAttribute('aria-label')",
                                sid)
            c.check(f"{label}: during {state} the picture's text alternative is in the "
                    "accessibility tree", f'img "{alt[:40]}' in snap.replace("\\", ""), snap[:300])
            if state in ("keyboard focus", "click", "tap"):
                ring = during["ring"]
                ratio = contrast(ring[2], bg) if ring[2].startswith("rgb") else 0
                c.check(f"{label}: {state} focuses the picture, with a ring of at least 3:1",
                        during["focused"] and ring[0] == "solid" and ring[1] == "3px" and
                        ratio >= 3.5, f"{ring} on {bg}: {ratio:.2f}")
        c.check(f"{label}: after {state} the picture is back and follows its clock without "
                "seeking", after["live"] == "visible" and after["stage"] == "visible" and
                after["liveOpacity"] == "1" and verdict is True, f"{after['live']} {numbers}")
        c.check(f"{label}: {state}: no console error", not errors, str(errors[:2]))
        ctx.close()
    cmp.close()


def still_checks(c, browser, base, url, sids, label, helpers, shots=None):
    """Hover and keyboard focus in both themes and at two widths, on every motion of the page:
    exactly one still picture, the poster key's file in the theme, in the stage's box; the
    picture's text alternative stays in the accessibility tree; a ring of 3:1 on focus."""
    new_page, goto = helpers["new_page"], helpers["goto"]
    for scheme in ["light", "dark"]:
        for width in [1440, 390]:
            ctx, page = new_page(browser, color_scheme=scheme,
                                 viewport={"width": width, "height": 900})
            goto(page, base + url)
            for sid in sids:
                shown = page.evaluate("""(sid) => { const s = document.getElementById(sid);
                  const n = document.getElementById(sid.slice(0, -3) + '-mn');
                  return n && getComputedStyle(n).visibility === 'visible' ? n.id : s.id; }""",
                                      sid)
                stage = page.locator(f"[id='{shown}']").locator("xpath=ancestor::div[1]")
                stage.scroll_into_view_if_needed()
                for state in ["hover", "keyboard focus"]:
                    enter(page, state, stage, shown)
                    page.wait_for_timeout(250)
                    during = page.evaluate(STATE, shown)
                    why = still_problem(page, shown, during, scheme == "dark")
                    ok = why is None and during["liveOpacity"] == "0"
                    c.check(f"{label} {scheme} {width} px: {state} on {shown} shows exactly the "
                            "poster key's still, in its box", ok, f"{why} {during['stills']}")
                    if shots and state == "hover" and scheme == "light" and sid == sids[-1]:
                        page.screenshot(path=f"{shots}/hover-light-{width}-{shown}.png")
                    if state == "keyboard focus":
                        bg = page_background(page)
                        ratio = contrast(during["ring"][2], bg)
                        c.check(f"{label} {scheme} {width} px: the focus ring of {shown} has "
                                "at least 3:1 against the page", ratio >= 3.5,
                                f"{during['ring']} on {bg}: {ratio:.2f}")
                    leave(page, state)
            ctx.close()


def motion_checks(c, browser, base, url, label, helpers, expect=None, shots=None, least=1):
    """The checks of the module docstring on the page `url` of the site at `base`, which must
    show at least `least` motions; `expect` is the folder of expectations."""
    new_page, goto, reports = helpers["new_page"], helpers["goto"], helpers["figure_reports"]
    ctx, page = new_page(browser, viewport={"width": 1440, "height": 900})
    errors = []
    page.on("console", lambda m: errors.append(m.text) if console_error(m) else None)
    goto(page, base + url)
    sids = motion_ids(page)
    blueprint = page.locator("a.bp_motion_link").count() > 0
    c.check(f"{label}: the page shows its motions inline", len(sids) >= least, str(sids))
    # positions, from the expectations: every rendition of every motion must have them
    missing = []
    cycle = 0.0
    for sid in sids:
        for suffix, vw in [("", 1440), ("-narrow", 360)]:
            target = sid if not suffix else sid[:-len("-mw")] + "-mn"
            if suffix and not page.evaluate("(t) => !!document.getElementById(t)", target):
                continue
            name = file_of(page, sid) + suffix
            path = os.path.join(expect, name + ".json") if expect else None
            if not path or not os.path.exists(path):
                missing.append(name)
                continue
            with open(path) as f:
                spec = json.load(f)
            cycle = max(cycle, spec.get("cycle", 0.0))
            vctx, vpage = new_page(browser, viewport={"width": vw, "height": 900})
            goto(vpage, base + url)
            position_checks(c, vpage, target, spec, f"{label} {name} ({vw} px)")
            vctx.close()
    c.check(f"{label}: every motion shown has its expectations", not missing,
            f"none in {expect} for {missing}")
    # it moves by itself
    # sampled for longer than the longest cycle (from the expectations), all at once
    seen = {sid: [] for sid in sids}
    for _ in range(max(24, min(200, int((cycle + 1) / 0.3) + 1))):
        for sid in sids:
            seen[sid].append(page.evaluate(READ, [sid, None]))
        page.wait_for_timeout(300)
    moving = [s[-1]["time"] > s[0]["time"] and any(
        math.dist(x[1], y[1]) > 0.5 for a, b in zip(s, s[1:])
        for x, y in zip(a["actors"], b["actors"])) for s in seen.values()]
    c.check(f"{label}: every moving picture plays on its own clock", all(moving), str(moving))
    # ids, actors
    ids = page.evaluate("""() => { const all = [...document.querySelectorAll('[id]')]
      .map(e => e.id); return all.filter((v, i) => all.indexOf(v) !== i); }""")
    c.check(f"{label}: every id of the page is there once", not ids, str(ids[:5]))
    shared = page.evaluate("""() => { const owner = {}; const out = [];
      for (const svg of document.querySelectorAll('svg.pilean-inline-svg'))
        for (const g of svg.querySelectorAll('[data-pilean-actor]')) {
          const a = g.getAttribute('data-pilean-actor');
          if (owner[a] && owner[a] !== svg.id) out.push(a); owner[a] = svg.id; }
      return out; }""")
    c.check(f"{label}: no actor is named in two pictures", not shared, str(shared[:5]))
    # accessibility: the captions while the stills are hidden, nothing announced
    listed = page.locator(".pilean-motion:not(.pilean-motion-bare)")
    if listed.count():
        snap = listed.first.aria_snapshot()
        hidden = page.evaluate("""() => document.querySelector('.pilean-motion-keys')
          .getBoundingClientRect().height""")
        c.check(f"{label}: the stills' captions are in the accessibility tree while hidden",
                hidden <= 1 and "Step 1 of" in snap and "listitem" in snap, snap[:300])
    hints = page.evaluate("""() => [...document.querySelectorAll('figure .pilean-motion')].map(m =>
      { const h = m.closest('figure').querySelector('figcaption .pilean-motion-hint');
        return h && h.offsetParent !== null && h.textContent; })""")
    c.check(f"{label}: every motion's caption says that it pauses on a still",
            all(h and "pauses on a still" in h for h in hints), str(hints))
    live = page.evaluate("""() => [...document.querySelectorAll('.pilean-motion')].some(m =>
      m.querySelector('[aria-live], [role=status], [role=alert]'))""")
    page.wait_for_timeout(500)
    c.check(f"{label}: nothing is announced while the pictures move",
            not live and not page.evaluate("window.__liveChanges"),
            str(page.evaluate("window.__liveChanges")))
    c.check(f"{label}: no content-policy report", not reports(page), str(reports(page)))
    # theme switched mid-animation
    # an element of the moving picture whose fill the theme rules restyle
    colour = """(sid) => { const svg = document.getElementById(sid);
      const css = svg.querySelector(':scope > style.pilean-theme').textContent;
      const e = [...svg.querySelectorAll('.pilean-motion-live [fill]')].find(e =>
        css.includes('[fill="' + e.getAttribute('fill') + '"]'));
      return e ? [e.getAttribute('fill'), getComputedStyle(e).fill] : null; }"""
    sid = next((s for s in reversed(sids) if page.evaluate(colour, s)), sids[0])
    light = page.evaluate(colour, sid) or ["", ""]
    t0 = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)
    page.evaluate("document.documentElement.setAttribute('data-theme', 'dark')")
    page.wait_for_timeout(100)
    dark = page.evaluate(colour, sid) or ["", ""]
    pair = page.evaluate("""([sid, fill]) => { const css = document.getElementById(sid)
      .querySelector(':scope > style.pilean-theme').textContent;
      const m = css.match(new RegExp('\\\\[fill="' + fill + '"\\\\]\\\\{fill:(#[0-9a-f]{6})\\\\}'));
      return m ? m[1] : null; }""", [sid, light[0]])

    def rgb(h):
        return f"rgb({int(h[1:3], 16)}, {int(h[3:5], 16)}, {int(h[5:7], 16)})" if h else None
    page.wait_for_timeout(600)
    t1 = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)
    c.check(f"{label}: switching the theme while it moves recolours the picture, which moves on",
            dark[1] == rgb(pair) and light[1] != dark[1] and t1 > t0,
            f"{light} -> {dark} (rule {pair}), {t0:.2f} -> {t1:.2f} s")
    page.evaluate("document.documentElement.removeAttribute('data-theme')")
    if blueprint:
        link = page.locator("figure a.bp_motion_link").first
        visible = link.is_visible()
        link.click()
        page.wait_for_timeout(200)
        focused = page.evaluate("""() => !!(document.activeElement &&
          document.activeElement.closest('#bp-motion'))""")
        c.check(f"{label}: the caption's link leads to the motion switch", visible and focused,
                f"{visible} {focused}")
    if shots:
        page.screenshot(path=f"{shots}/motion-states-1440-on.png", full_page=True)
    c.check(f"{label}: no console error on the page", not errors, str(errors[:3]))
    ctx.close()
    # print
    ctx, page = new_page(browser, viewport={"width": 1100, "height": 900})
    goto(page, base + url)
    page.emulate_media(media="print")
    page.wait_for_timeout(200)
    printed = [page.evaluate(STATE, s) for s in sids]
    c.check(f"{label}: printed, every motion shows its stills or its poster's still and not its "
            "moving picture, by visibility or opacity only",
            all(p["stageDisplay"] != "none" and
                ((p["live"] == "hidden" and p["keysDisplay"] == "grid" and p["keys"] > 20) or
                 (p["liveOpacity"] == "0" and p["still"] == "1")) and p["hint"] is not True
                for p in printed), str(printed[:1]))
    ctx.close()
    # narrow and wide renditions
    narrow_sids = [s for s in sids if page_has_narrow(browser, base, url, s, helpers)]
    for width, shown, other in [(1440, "mw", "mn"), (360, "mn", "mw")]:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        goto(page, base + url)
        res = []
        for s in narrow_sids:
            base_id = s[:-len("-mw")]
            res.append(page.evaluate("""([a, b]) => { const x = document.getElementById(a),
              y = document.getElementById(b); const st = x.parentElement;
              return [getComputedStyle(x).visibility, getComputedStyle(y).visibility,
                getComputedStyle(y).position,
                Math.abs(st.getBoundingClientRect().height - x.getBoundingClientRect().height)];
              }""", [f"{base_id}-{shown}", f"{base_id}-{other}"]))
        if narrow_sids:
            c.check(f"{label} {width} px: the {'wide' if shown == 'mw' else 'narrow'} rendition "
                    "is shown and the other takes no space",
                    all(r[0] == "visible" and r[1] == "hidden" and r[2] == "absolute" and r[3] < 1
                        for r in res), str(res))
        ctx.close()
    for width in [360, 768, 1440]:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        goto(page, base + url)
        wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
        c.check(f"{label} {width} px: no sideways scrolling", wide <= 0, f"{wide} px")
        ctx.close()
    # states, with the freeze check, on every motion of the page
    for sid in sids:
        state_checks(c, browser, base, url, sid, label, helpers, blueprint)
    still_checks(c, browser, base, url, sids, label, helpers, shots)


def page_has_narrow(browser, base, url, sid, helpers):
    ctx, page = helpers["new_page"](browser, viewport={"width": 800, "height": 600})
    helpers["goto"](page, base + url)
    has = page.evaluate("(sid) => !!document.getElementById(sid.slice(0, -3) + '-mn')", sid)
    ctx.close()
    return has


MOTION_MARK = re.compile(r'<div class="pilean-motion(?: [^"]*)?" data-bp-motion')


def motion_pages(site):
    """The addresses, relative to the site's root, of its pages that show a motion."""
    out = []
    for root, _, files in os.walk(site):
        if "index.html" in files:
            with open(os.path.join(root, "index.html"), encoding="utf-8") as f:
                if MOTION_MARK.search(f.read()):
                    rel = os.path.relpath(root, site)
                    out.append("" if rel == "." else rel.replace(os.sep, "/") + "/")
    return sorted(out)


def main(argv):
    from playwright.sync_api import sync_playwright
    import site_browser
    if not argv or argv[1:2] != ["--expect"] or len(argv) not in (3, 5):
        print("usage: motion_browser.py SITE_DIR --expect DIR [--shots DIR]")
        return 2
    site, expect = argv[0], argv[2]
    shots = argv[4] if len(argv) == 5 and argv[3] == "--shots" else None
    helpers = {"new_page": site_browser.new_page, "goto": site_browser.goto,
               "figure_reports": site_browser.figure_reports}
    c = site_browser.Checks()
    pages = motion_pages(site)
    server, base = site_browser.serve(site)
    with sync_playwright() as p:
        browser = p.chromium.launch()
        c.check("the site has pages with motions", bool(pages), site)
        c.section("freeze control", freeze_control, c, browser)
        for url in pages:
            c.section(f"motions of {url}", motion_checks, c, browser, base, url, url or "/",
                      helpers, expect, shots)
        browser.close()
    server.shutdown()
    print(f"motions: {c.count - c.failed} of {c.count} hold")
    return 1 if c.failed else 0


if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    sys.exit(main(sys.argv[1:]))
