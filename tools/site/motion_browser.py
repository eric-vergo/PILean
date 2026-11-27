# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""The browser checks of motions shown in the pages of a site built with the Verso adapters (one
of PILean's site checks, `tools/site/`):

    python3 tools/site/motion_browser.py SITE_DIR --expect DIR [--shots DIR] [--workers N]
        [--engine chromium|firefox]

SITE_DIR is the generator's `html-multi` folder; every page with a motion (`data-bp-motion`) is
checked. DIR holds the expectations of every motion shown, `<file>.json` for the animated SVG
`<file>.svg` of each rendition (`<decl>.json`, `<decl>-narrow.json`), in the form PILean's tests
write them (`PILeanTest.MotionChecks.expectations`, `PILeanTest.MotionPanelsChecks.expectations`);
a motion without its expectations fails. The site is served on 127.0.0.1 under a strict content
policy (`site_browser.serve`) and checked in Chromium (Playwright, nothing installed or downloaded).
`--engine firefox` runs the same checks in Playwright's Firefox, with the freeze control (a freeze
seen in Chromium) and the PDF print (which Playwright makes in Chromium only) reported as not
applicable (`n/a:` lines); every other check runs there as in Chromium. `--workers N` checks N
pages at a time, each in a process with its own browser. `motion_checks` checks one page; on a
Blueprint site (a caption with the switch's link) also the switch and the link. Checked:
* with the clock paused and set, in the first loop and again one cycle later, every actor of the
  page's moving picture is where its key still has it at every rest (0.05 px), on its circle at a
  quarter, a half and three quarters of every turn (0.05 px, a true arc) at the eased angle (0.5
  degrees), on the straight segment between its keys at the eased fraction at the same times of
  every slide (0.05 px; a motion may have no turn or no slide), every label and marker upright (0.01
  degrees), and every panel of a picture of panels in phase with the others (0.05 px); this covers
  the actors' anchors and the upright marks, not every pixel (`tools/motion-browser-check.py`
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
  the page, and a click holds the still after the pointer has left; after each of them ends the
  moving picture follows its clock again without being sought (the regression test for a picture
  frozen after it was hidden; the check is shown to notice a picture hidden with `display:
  none`). Each state starts inside one key's rest and the picture is compared inside a later
  key's rest that certainly draws another picture (`rest_pair`, from the expectations), so that
  a frozen picture and a running one cannot look the same; a comparison that stays undecided
  fails;
* free-running, without seeking, every picture is where its keys have it inside two of its rests
  that differ, and its clock has advanced (`free_running`);
* at seven widths from 1440 to 320 px the page does not scroll sideways, with motion on and off,
  and with motion off every still of every grid of stills (inline and on a figure's page) is
  shown at `STILL_FRACTION` of its natural width or more, or fills its column alone, and never
  larger than its natural width (`grid_checks`);
* the captions are in the accessibility tree while the stills are hidden, and nothing is
  announced (no live region changes);
* every id of the page once, and no `data-pilean-actor` in two pictures;
* the caption's note, exactly `HINT` (a still replaces the picture while it is pointed at or
  focused, or after a click or tap until a click elsewhere), shown only while motion is on; on a
  Blueprint site the caption's link leads to the motion switch;
* no content-policy report about a figure and no console error.
"""

import base64
import json
import math
import os
import re
import sys

# The note every motion's caption ends with (`PILeanVerso.motionHintText`): while a still covers
# the picture its clock runs on, so it is said as a still that replaces it, not as a pause.
HINT = ("Animation; a still replaces it while you point at it or focus it, or after a click or "
        "tap until you click elsewhere.")

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
    reports of figures are checked by `figure_reports`), in Chromium's words ("inline event
    handler") or Firefox's ("blocked an event handler", naming the table of contents' toggle)."""
    return m.type == "error" and "inline event handler" not in m.text and not (
        "blocked an event handler" in m.text and "toggle-toc" in m.text)


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
    """Rests, arcs, slides, uprights and phase of one moving picture against the expectations, in
    its first loop and again one cycle later (the clock paused and set)."""
    page.evaluate("(sid) => document.getElementById(sid).pauseAnimations()", sid)
    rest_err = radius_err = angle_err = upright = 0.0
    missing = []
    counts = set()
    loops = [(k * spec["cycle"], r) for k in (0, 1) for r in spec["rests"]]
    for off, rest in loops:
        seen = page.evaluate(READ, [sid, rest["t"] + off])
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
        for off, sample in [(k * spec["cycle"], sm) for k in (0, 1) for sm in turn["samples"]]:
            seen = page.evaluate(READ, [sid, sample["t"] + off])
            upright = max([upright] + [abs(a) for a, _ in seen["uprights"]])
            xy = first(seen["actors"], turn["id"])
            if xy is None:
                missing.append(turn["id"])
                continue
            radius_err = max(radius_err, abs(math.dist(xy, cc) - r))
            if r >= 1:
                a = math.degrees(math.atan2(xy[1] - cc[1], xy[0] - cc[0]))
                angle_err = max(angle_err, abs(wrap((a - a0) - turn["sweep"] * sample["f"])))
    slide_err = 0.0
    for sl in spec.get("slides", []):
        a, b = sl["from"], sl["to"]
        for off, sample in [(k * spec["cycle"], sm) for k in (0, 1) for sm in sl["samples"]]:
            seen = page.evaluate(READ, [sid, sample["t"] + off])
            upright = max([upright] + [abs(x) for x, _ in seen["uprights"]])
            xy = first(seen["actors"], sl["id"])
            if xy is None:
                missing.append(sl["id"])
                continue
            f = sample["f"]
            slide_err = max(slide_err, math.dist(xy, [a[0] + f * (b[0] - a[0]),
                                                       a[1] + f * (b[1] - a[1])]))
    c.check(f"{label}: at every rest each actor and upright mark is where the key still has it",
            not missing and rest_err <= REST_TOL and counts == {spec["uprights"]},
            f"{rest_err:.3g} px, missing {missing[:3]}, uprights {counts}")
    if spec["turns"]:
        c.check(f"{label}: every turn is a true arc at the eased angle",
                radius_err <= RADIUS_TOL and angle_err <= ANGLE_TOL,
                f"{radius_err:.3g} px, {angle_err:.3g} deg over {len(spec['turns'])} turns")
    if spec.get("slides"):
        c.check(f"{label}: every slide keeps its actor on the straight segment between its keys, "
                "at the eased fraction", slide_err <= REST_TOL,
                f"{slide_err:.3g} px over {len(spec['slides'])} slides")
    c.check(f"{label}: labels and markers stay upright", upright <= UPRIGHT_TOL, f"{upright:.3g}")
    if spec.get("phase"):
        err, bad = 0.0, 0
        for off, sample in [(k * spec["cycle"], sm) for k in (0, 1) for sm in spec["phase"]]:
            seen = page.evaluate(READ, [sid, sample["t"] + off])
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


def wait_clock(page, sid, t, cycle, early=0.0, late=0.15):
    """Waits until the running clock of the picture `sid` is between `early` seconds before `t`
    and `late` seconds after it, modulo the cycle, and returns its time then; `None` if it does
    not get there within two cycles."""
    for _ in range(int((2 * cycle + 2) / 0.015)):
        now = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)
        if 0 <= (now - t + early) % cycle <= early + late:
            return now
        page.wait_for_timeout(15)
    return None


# Seconds of the motion's clock. A state starts inside one rest and ends `SHOW_LEAD` before the
# moment of comparison; that moment comes at least `MIN_HELD` after the start for a way of turning
# motion off (so the state lasts 1.3 s or more, while its stills load) and at least `MIN_COVERED`
# after it for hover, focus, a click or a tap (0.4 s or more). Without the rests' ends in the
# expectations, a probe starts within `NEAR_REST` of a rest's middle.
SHOW_LEAD = 0.5
MIN_HELD = 1.8
MIN_COVERED = 0.9
NEAR_REST = 0.25

# The version of the expectations' format these checks read (`PILeanTest.MotionChecks
# .expectationsFormat`), and what it has that an older one lacks.
FORMAT = 2


def spec_problem(spec):
    """Why the expectations cannot be checked by this tool, or `None`: written in an older format
    (a writer built with an older PILean, without the rests' ends, the slides, the declared moves
    and the actors' drawings, so that a slide would go unchecked), or listing other turns or
    slides than the motion declares (a writer that lost some)."""
    if spec.get("format", 1) < FORMAT or "declared" not in spec or "slides" not in spec or \
            any("shapes" not in r or "from" not in r for r in spec["rests"]):
        return (f"the expectations are in format {spec.get('format', 1)}, this check reads format "
                f"{FORMAT} (rests with their ends and drawings, slides, declared moves): rebuild "
                "the expectations writer with this version of PILean")
    d = spec["declared"]
    if d["turns"] != len(spec["turns"]) or d["slides"] != len(spec["slides"]):
        return (f"the motion declares {d['turns']} turns and {d['slides']} slides, the "
                f"expectations list {len(spec['turns'])} and {len(spec['slides'])}")
    return None


def rests_differ(a, b):
    """Whether two rests of the expectations certainly draw different pictures: an actor is in one
    and not the other, an actor's anchor is more than a pixel apart, or an actor is drawn
    otherwise (its fingerprint in `shapes` differs: a morph, whose anchor may stay)."""
    at_a = {x["id"]: x["at"] for x in a["actors"]}
    at_b = {x["id"]: x["at"] for x in b["actors"]}
    return at_a.keys() != at_b.keys() or any(math.dist(at_a[k], at_b[k]) > 1 for k in at_a) or \
        a.get("shapes", {}) != b.get("shapes", {})


def undecided(spec):
    """Why no probe on the timeline can be chosen (`rest_pair` gave none)."""
    if len(spec["rests"]) < 2:
        return "the probe could not run: the motion has a single rest"
    return ("the probe could not run: no two rests of the motion certainly draw different "
            "pictures (same actors, anchors and drawings)")


def rest_window(rest):
    """The part of a rest (seconds of the clock) where a probe may read or switch: the rest less
    0.1 s at each end, from its start and end in the expectations, else `NEAR_REST` about its
    middle."""
    if "from" in rest and rest["until"] - rest["from"] > 0.3:
        return rest["from"] + 0.1, rest["until"] - 0.1
    return rest["t"] - NEAR_REST, rest["t"] + NEAR_REST


def rest_pair(spec, start, least):
    """A probe on the motion's timeline for a clock at `start`: it starts inside the window
    (`rest_window`) of one rest, at once when the clock is there already, and ends at a time
    inside the window of another rest that certainly draws another picture (`rests_differ`), at
    least `least` seconds after it starts and at least 0.2 s before that window closes; the probe
    that is over soonest, as `(first rest, its window, second rest, the time to compare at)`, or
    `None` when no two rests certainly differ."""
    cycle = spec["cycle"]
    best = None
    for a in spec["rests"]:
        lo_a, hi_a = rest_window(a)
        if (start - lo_a) % cycle <= hi_a - lo_a:
            wait, begin = 0.0, start
        else:
            wait, begin = (lo_a - start) % cycle, lo_a
        for b in spec["rests"]:
            if not rests_differ(a, b):
                continue
            lo_b, hi_b = rest_window(b)
            hi_b = max(lo_b, hi_b - 0.2)
            d = (lo_b - begin) % cycle
            if d >= least:
                off = d
            elif (begin + least - lo_b) % cycle <= hi_b - lo_b:
                off = least
            else:
                off = d + cycle
            if best is None or wait + off < best[0]:
                best = (wait + off, a, (lo_a, hi_a), b, (begin + off) % cycle)
    return best and best[1:]


def follows_clock(page, sid, hidden_at, cmp, pause_at=None, cycle=None):
    """Whether the moving picture, shown again, draws the time of its running clock: paused
    without seeking (400 ms after it was shown again, or when its clock reaches `pause_at`
    modulo `cycle`), its picture matches the picture of that time (sought) better than half as
    well as the picture of the time it was hidden, which a frozen picture matches. Returns the
    verdict and the numbers; `None` as verdict when the two times draw the same picture. The
    pictures are compared in `cmp`, a blank page of its own (the site's policy loads no `data:`
    image)."""
    if pause_at is None:
        page.wait_for_timeout(400)
    else:
        wait_clock(page, sid, pause_at, cycle)
    page.evaluate("(sid) => document.getElementById(sid).pauseAnimations()", sid)
    page.wait_for_timeout(120)
    drawn = shot(page, sid)
    now = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)

    def at(t):
        page.evaluate("([sid, t]) => document.getElementById(sid).setCurrentTime(t)", [sid, t])
        page.wait_for_timeout(80)
        return shot(page, sid)
    # the times within 40 ms of the pause, nearest first; a perfect match ends the search
    best = None
    for k in (0, -1, 1, -2, 2, -3, 3, -4, 4):
        n = cmp.evaluate(PIXELS, [uri(drawn), uri(at(now + 0.01 * k))])
        best = n if best is None else min(best, n)
        if best == 0:
            break
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


def prepare(page, state, stage):
    """What a state needs before it starts at a chosen moment: for keyboard focus, Tab from the
    start of the page until the stage is focused (it is a tab stop), then one step back, so that
    one Tab in `enter` focuses it. Returns whether the walk reached the stage."""
    if state != "keyboard focus":
        return True
    reached = False
    for _ in range(400):
        page.keyboard.press("Tab")
        if stage.evaluate("e => document.activeElement === e"):
            reached = True
            break
    page.keyboard.press("Shift+Tab")
    return reached


def enter(page, state, stage, sid, prepared=False):
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
        # the stage is a tab stop: Tab from the elements before it reaches it (with `prepared`,
        # `prepare` has walked there and stepped back once, so one Tab focuses it)
        for _ in range(1 if prepared else 400):
            page.keyboard.press("Tab")
            if stage.evaluate("e => document.activeElement === e"):
                break
    elif state == "click":
        # the still stays after the pointer has left: the click's focus holds it, as the
        # caption's note says
        stage.click()
        page.mouse.move(2, 2)
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


def freeze_control(c, browser, engine="chromium"):
    """The freeze check must notice a picture hidden with `display: none`: on the fixture
    `fixtures/freeze.html` (one rotation in one segment of 8 seconds, hidden with `display: none`
    under `data-motion="reduce"`), hidden for 1.2 seconds and shown again, it must find the
    picture frozen, on each of three runs. Chromium leaves a picture whose transform is animated
    frozen until the animation repeats when it is shown again after `display: none` (the
    rotation of the fixture, every time); an animation of `opacity` mostly is not (once in eight
    runs), and a picture that draws the same at the two times (a rest that spans both) shows
    nothing either, which is why the real check takes its moments from the motion's timeline
    (`rest_pair`) and the control uses a picture that moves all the time."""
    if engine != "chromium":
        # Firefox 159 does not freeze the fixture: shown again after display: none it follows its
        # clock (measured on three runs), so the control has nothing to show there
        c.say(f"n/a: the freeze control in {engine}: the freeze it shows is Chromium's (Firefox "
              "follows its clock after display: none); the check that every picture follows its "
              "clock after every hide runs in every engine")
        return
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


def state_checks(c, browser, base, url, sid, label, helpers, blueprint, spec=None,
                 only_off=False):
    """Each way of turning motion off, and hover and focus, on the moving picture `sid`: what is
    shown, and that the picture follows its clock afterwards. With the motion's expectations
    `spec`, each state starts inside one key's rest and ends just before a moment inside a later
    key's rest that certainly draws another picture, where the picture is compared
    (`rest_pair`); without them it is held for 1.3, 2.1 and then 3.7 seconds until the two times
    draw different pictures. A comparison that stays undecided fails. With `only_off`, the ways of
    turning motion off, hover and keyboard focus only (not a click, a tap or a PDF print, whose
    stage and rules are checked where the stills are listed)."""
    new_page, goto = helpers["new_page"], helpers["goto"]
    engine = helpers.get("engine", "chromium")
    states = list(OFF[:2]) + (["switch"] if blueprint else []) + ["print", "hover",
                                                                    "keyboard focus"] + \
        ([] if only_off else ["pdf", "click", "tap"])
    if engine != "chromium" and "pdf" in states:
        # Playwright prints a PDF in Chromium only
        states.remove("pdf")
        c.say(f"n/a: {label}: printing a PDF in {engine} (Playwright prints in Chromium only)")
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
        prepared = prepare(page, state, stage)
        clock = "(sid) => document.getElementById(sid).getCurrentTime()"
        least = MIN_HELD if state in OFF else MIN_COVERED
        times = spec and rest_pair(spec, page.evaluate(clock, sid) + 0.1, least)
        for hold in ((None,) if times else (1300, 2100, 3700)):
            if times:
                _, (lo, hi), _, at = times
                wait_clock(page, sid, lo, spec["cycle"], 0.0, hi - lo)
            hidden_at = page.evaluate(clock, sid)
            enter(page, state, stage, sid, prepared)
            if state in OFF:
                # the stills are pictures loaded lazily: bring the list into view, as a reader who
                # turned motion off sees it (Firefox loads a lazy picture only near the view)
                page.evaluate("""(sid) => { const k = document.getElementById(sid)
                  .closest('.pilean-motion').querySelector('.pilean-motion-keys');
                  if (k) k.scrollIntoView({block: 'nearest'}); }""", sid)
            if times:
                wait_clock(page, sid, at - SHOW_LEAD, spec["cycle"])
            else:
                page.wait_for_timeout(hold)
            during = page.evaluate(STATE, sid)
            snap = page.locator(f"[id='{sid}']").locator("xpath=ancestor::div[2]").aria_snapshot()
            bg = page_background(page)
            leave(page, state)
            after = page.evaluate(STATE, sid)
            if times:
                verdict, numbers = follows_clock(page, sid, hidden_at, cmp, at, spec["cycle"])
                if verdict is None:
                    numbers = ("undecided: the two moments drew the same picture, although their "
                               "rests differ",) + tuple(numbers)
            else:
                verdict, numbers = follows_clock(page, sid, hidden_at, cmp)
                if spec:
                    numbers = (undecided(spec),) + tuple(numbers)
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


# The least fraction of its natural width a still is shown at, unless it fills its column
# (`PILeanVerso.stillFraction`).
STILL_FRACTION = 0.75

GRID = """() => {
  const grids = [...document.querySelectorAll(
    '.pilean-motion:not(.pilean-motion-bare) ol.pilean-motion-keys, ol.pilean-page-motion-keys')];
  return grids.map(ol => {
    const home = ol.closest('.pilean-motion') || ol.closest('.pilean-figure-page');
    const live = home && home.querySelector('svg.pilean-motion-wide');
    const items = [...ol.children];
    const lefts = new Set(items.map(li => Math.round(li.getBoundingClientRect().left)));
    const imgs = items.map(li => [...li.querySelectorAll('img')].find(i => i.offsetParent !== null))
      .filter(i => i);
    return {file: live ? live.getAttribute('data-pilean-file') : '?', page: !!ol.closest(
        '.pilean-figure-page') && ol.classList.contains('pilean-page-motion-keys'),
      grid: ol.getBoundingClientRect().width, columns: lefts.size, items: items.length,
      stills: imgs.map(i => [Math.round(i.getBoundingClientRect().width * 10) / 10,
        i.naturalWidth, i.complete])};
  });
}"""


def grid_checks(c, browser, base, url, label, helpers, shots=None, layouts=None):
    """At 1440, 1024, 768, 560, 390, 360 and 320 px the page does not scroll sideways with motion
    on, and with motion off: every still of every grid of stills (inline and on a figure's page)
    is shown at `STILL_FRACTION` of its natural width or more, or fills its column alone, no still
    is drawn larger than its natural width (the narrow rendition's at small widths), and the page
    does not scroll sideways. Records the number of columns of each motion's grid in `layouts` (by
    its file, the page's grid apart), and with `shots` saves a picture of each grid."""
    new_page, goto = helpers["new_page"], helpers["goto"]
    for width in [1440, 1024, 768, 560, 390, 360, 320]:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        goto(page, base + url)
        on = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
        c.check(f"{label} {width} px: no sideways scrolling", on <= 0, f"{on} px")
        page.evaluate("""() => { document.documentElement.setAttribute('data-motion', 'reduce');
          for (const i of document.querySelectorAll('.pilean-motion-keys img,'
            + ' .pilean-page-motion-keys img')) i.loading = 'eager'; }""")
        page.wait_for_function("""() => [...document.querySelectorAll('.pilean-motion-keys img,'
          + ' .pilean-page-motion-keys img')].every(i => i.offsetParent === null || i.complete)""",
                               timeout=10000)
        grids = page.evaluate(GRID)
        wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
        bad, big = [], []
        for g in grids:
            for w, natural, done in g["stills"]:
                fills = g["columns"] == 1 and w >= min(natural, g["grid"]) - 1
                if not done or natural == 0 or not (w >= STILL_FRACTION * natural - 1 or fills):
                    bad.append((g["file"], w, natural, g["columns"], g["grid"]))
                if w > natural + 1:
                    big.append((g["file"], w, natural))
            if layouts is not None:
                key = (os.path.basename(g["file"]), "page" if g["page"] else "inline")
                layouts.setdefault(key, {})[width] = g["columns"]
        c.check(f"{label} {width} px: with motion off every still is shown at "
                f"{STILL_FRACTION} of its natural width or more, or fills its column",
                bool(grids) and not bad and all(g["stills"] for g in grids),
                f"{[(g['file'], g['columns'], g['stills'][:1]) for g in grids]}; off: {bad[:3]}")
        c.check(f"{label} {width} px: with motion off no still is drawn larger than its natural "
                "width", bool(grids) and not big, str(big[:3]))
        c.check(f"{label} {width} px: with motion off no sideways scrolling", wide <= 0,
                f"{wide} px")
        if shots and width in (1440, 768, 560, 390):
            loc = page.locator(".pilean-motion:not(.pilean-motion-bare) ol.pilean-motion-keys,"
                               " ol.pilean-page-motion-keys")
            for i in range(loc.count()):
                stem = re.sub(r"[^A-Za-z0-9._-]", "_", (url or "root").strip("/"))
                loc.nth(i).screenshot(path=f"{shots}/grid-{stem}-{i}-{width}.png")
        ctx.close()


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
                    if why is None and during["liveOpacity"] != "0":
                        why = (f"the moving picture's opacity is {during['liveOpacity']}, "
                               "not 0")
                    c.check(f"{label} {scheme} {width} px: {state} on {shown} shows exactly the "
                            "poster key's still, in its box", why is None,
                            f"{why}; the pictures with a box: {during['stills']}")
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


def free_running(page, sids, specs, timeout=None):
    """Without seeking, while every clock runs: for each motion, the clock is read inside two
    rests that certainly draw different pictures (`rest_pair`), every actor's anchor read there
    must be where its key's still has it, and the clock must have advanced between the two. All
    the motions of the page are watched at once, so the wait is that of the slowest. Returns, per
    motion, `(problem, largest distance in px)`, the problem `None` when it holds."""
    clock = "(ids) => ids.map(i => document.getElementById(i).getCurrentTime())"
    todo, out = {}, {}
    for sid in sids:
        spec = specs[sid]
        now = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)
        pair = rest_pair(spec, now + 0.1, 0.6)
        if not pair:
            out[sid] = (undecided(spec), 0.0)
            continue
        a, (lo, hi), b, at = pair
        todo[sid] = {"spec": spec, "targets": [(a, lo, hi), (b, at, at + 0.15)], "seen": []}
    limit = timeout or 2 * max([d["spec"]["cycle"] for d in todo.values()] + [1]) + 2
    deadline = page.evaluate("performance.now()") + limit * 1000
    while todo and page.evaluate("performance.now()") < deadline:
        ids = list(todo)
        for sid, now in zip(ids, page.evaluate(clock, ids)):
            d = todo[sid]
            rest, lo, hi = d["targets"][len(d["seen"])]
            if (now - lo) % d["spec"]["cycle"] <= hi - lo:
                seen = page.evaluate(READ, [sid, None])
                err = max([0.0] + [math.dist(xy, a["at"]) if xy is not None else math.inf
                                   for a in rest["actors"]
                                   for xy in [first(seen["actors"], a["id"])]])
                d["seen"].append((seen["time"], err))
                if len(d["seen"]) == 2:
                    (t1, e1), (t2, e2) = d["seen"]
                    e = max(e1, e2)
                    why = None
                    if t2 <= t1:
                        why = f"the clock did not advance ({t1:.2f} s, then {t2:.2f} s)"
                    elif e > REST_TOL:
                        why = f"an actor is {e:.3g} px from its key at a rest, not sought"
                    out[sid] = (why, e)
                    del todo[sid]
        page.wait_for_timeout(15)
    for sid, d in todo.items():
        out[sid] = (f"the clock did not reach the rests it was waited for within {limit:.0f} s "
                    f"({len(d['seen'])} of 2 read)", math.inf)
    return out


def motion_checks(c, browser, base, url, label, helpers, expect=None, shots=None, least=1):
    """The checks of the module docstring on the page `url` of the site at `base`, which must
    show at least `least` motions; `expect` is the folder of expectations. A motion shown without
    its stills (on its figure's page) whose stills are shown on another page of the site
    (`helpers["listed"]`, the files of `listed_motions`) gets the checks that differ between the
    two, and hover and keyboard focus once more, each with its still and its clock (the figure's
    page has rules of its own); a click, a tap, a PDF print and the stills in both themes use the
    same stage and rules, and are checked where the stills are listed."""
    new_page, goto, reports = helpers["new_page"], helpers["goto"], helpers["figure_reports"]
    ctx, page = new_page(browser, viewport={"width": 1440, "height": 900})
    errors = []
    page.on("console", lambda m: errors.append(m.text) if console_error(m) else None)
    goto(page, base + url)
    sids = motion_ids(page)
    blueprint = page.locator("a.bp_motion_link").count() > 0
    c.check(f"{label}: the page shows its motions inline", len(sids) >= least, str(sids))
    narrow_sids = [s for s in sids if page.evaluate(
        "(sid) => !!document.getElementById(sid.slice(0, -3) + '-mn')", s)]
    bare = {s: page.evaluate("(sid) => document.getElementById(sid).closest('.pilean-motion')"
                             ".classList.contains('pilean-motion-bare')", s) for s in sids}
    elsewhere = set(helpers.get("listed") or ())
    covered = {s for s in sids if bare[s] and os.path.basename(
        page.evaluate("(sid) => document.getElementById(sid).getAttribute('data-pilean-file')",
                      s)) in elsewhere}
    # the expectations: every rendition of every motion must have them, in this tool's format
    missing, bad = [], []
    specs, narrow_specs = {}, {}
    for sid in sids:
        for suffix in ["", "-narrow"]:
            if suffix and sid not in narrow_sids:
                continue
            name = file_of(page, sid) + suffix
            path = os.path.join(expect, name + ".json") if expect else None
            if not path or not os.path.exists(path):
                missing.append(name)
                continue
            with open(path) as f:
                spec = json.load(f)
            why = spec_problem(spec)
            if why:
                bad.append(f"{name}: {why}")
                continue
            (narrow_specs if suffix else specs)[sid] = spec
    c.check(f"{label}: every motion shown has its expectations", not missing,
            f"none in {expect} for {missing}")
    c.check(f"{label}: every motion's expectations can be checked", not bad, "; ".join(bad))
    # it moves by itself, before anything seeks its clock (a seek mends a picture frozen since the
    # page loaded): free-running, at two rests of its own timeline that differ, each picture is
    # where its keys have it and its clock has advanced; without expectations, sampled for longer
    # than the longest cycle, all at once
    if all(s in specs for s in sids):
        runs = free_running(page, sids, specs)
        c.check(f"{label}: every moving picture plays on its own clock and, not sought, is where "
                "its keys have it at two of its rests",
                all(r[0] is None for r in runs.values()),
                str({k: v[0] or f"{v[1]:.3g} px, clock advanced" for k, v in runs.items()}))
    else:
        seen = {sid: [] for sid in sids}
        cycle = max([sp["cycle"] for sp in specs.values()] + [0.0])
        for _ in range(max(24, min(200, int((cycle + 1) / 0.3) + 1))):
            for sid in sids:
                seen[sid].append(page.evaluate(READ, [sid, None]))
            page.wait_for_timeout(300)
        moving = [s[-1]["time"] > s[0]["time"] and any(
            math.dist(x[1], y[1]) > 0.5 for a, b in zip(s, s[1:])
            for x, y in zip(a["actors"], b["actors"])) for s in seen.values()]
        c.check(f"{label}: every moving picture plays on its own clock", all(moving),
                str(moving))
    # positions, with the clock paused and set: the wide rendition on this page, the narrow one at
    # 360 px
    for sid, spec in specs.items():
        position_checks(c, page, sid, spec, f"{label} {file_of(page, sid)} (1440 px)")
    if narrow_specs:
        nctx, npage = new_page(browser, viewport={"width": 360, "height": 900})
        goto(npage, base + url)
        for sid, spec in narrow_specs.items():
            position_checks(c, npage, sid[:-len("-mw")] + "-mn", spec,
                            f"{label} {file_of(page, sid)}-narrow (360 px)")
        nctx.close()
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
    c.check(f"{label}: every motion's caption says what hovering, a click and a tap do",
            all(h == HINT for h in hints), str(hints))
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
    for width, shown, other in [(1440, "mw", "mn"), (360, "mn", "mw")]:
        if not narrow_sids:
            break
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
        c.check(f"{label} {width} px: the {'wide' if shown == 'mw' else 'narrow'} rendition "
                "is shown and the other takes no space",
                all(r[0] == "visible" and r[1] == "hidden" and r[2] == "absolute" and r[3] < 1
                    for r in res), str(res))
        ctx.close()
    # sideways scrolling with motion on and off, and the grids of stills
    grid_checks(c, browser, base, url, label, helpers, shots, helpers.get("layouts"))
    # states, with the freeze check, on every motion of the page
    for sid in sids:
        state_checks(c, browser, base, url, sid, label, helpers, blueprint, specs.get(sid),
                     only_off=sid in covered)
    rest = [s for s in sids if s not in covered]
    if rest:
        still_checks(c, browser, base, url, rest, label, helpers, shots)
    if covered:
        c.check(f"{label}: a click, a tap, a PDF print and the stills in both themes of "
                f"{sorted(covered)} are checked where their stills are listed (the same stage "
                "and rules)", True)


def _page_job(job):
    """One page's motion checks in a process of its own (`motion_pages_checks`): its own
    Chromium, the verdicts kept and returned with the grids' columns."""
    base, url, label, expect, shots, least, listed, engine = job
    import site_browser
    from playwright.sync_api import sync_playwright
    c = site_browser.Checks(keep=True)
    helpers = {"new_page": site_browser.new_page, "goto": site_browser.goto,
               "figure_reports": site_browser.figure_reports, "layouts": {}, "listed": listed,
               "engine": engine}
    with sync_playwright() as p:
        browser = site_browser.launch(p, engine)
        c.section(f"motions of {url}", motion_checks, c, browser, base, url, label, helpers,
                  expect, shots, least)
        browser.close()
    return c.lines, c.count, c.failed, helpers["layouts"]


def motion_pages_checks(c, browser, base, jobs, helpers, expect, shots, workers=1):
    """`motion_checks` on every page of `jobs` (`(url, label, least)`), in order; with `workers`
    above 1, that many pages at a time, each in a process with its own Chromium (the pages are
    independent: each check opens its own contexts), the verdicts printed in the pages' order and
    counted in `c`, the grids' columns merged into `helpers["layouts"]`."""
    if workers <= 1:
        for url, label, least in jobs:
            c.section(f"motions of {url}", motion_checks, c, browser, base, url, label, helpers,
                      expect, shots, least)
        return
    import concurrent.futures
    import multiprocessing
    listed = set(helpers.get("listed") or ())
    engine = helpers.get("engine", "chromium")
    args = [(base, url, label, expect, shots, least, listed, engine)
            for url, label, least in jobs]
    with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers, mp_context=multiprocessing.get_context("spawn")) as pool:
        for lines, count, failed, layouts in pool.map(_page_job, args):
            for line in lines:
                c.say(line)
            c.count += count
            c.failed += failed
            if helpers.get("layouts") is not None:
                for k, v in layouts.items():
                    helpers["layouts"].setdefault(k, {}).update(v)


def listed_motions(site):
    """The files (base names of `data-pilean-file`) of the motions some page of the site shows
    with their list of stills, that is, not only on a figure's page."""
    out = set()
    wrapper = re.compile(r'<div class="(pilean-motion(?: [^"]*)?)" data-bp-motion[^>]*>')
    for root, _, files in os.walk(site):
        if "index.html" in files:
            with open(os.path.join(root, "index.html"), encoding="utf-8") as f:
                text = f.read()
            for m in wrapper.finditer(text):
                if "pilean-motion-bare" in m.group(1).split():
                    continue
                f = re.compile(r'data-pilean-file="([^"]+)"').search(text, m.end())
                if f:
                    out.add(os.path.basename(f.group(1)))
    return out


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
    opts = {}
    rest = list(argv[1:])
    try:
        engine = site_browser.engine_option(rest)
    except ValueError as e:
        print(f"motion_browser.py: {e}")
        return 2
    while rest and rest[0] in ("--expect", "--shots", "--workers") and len(rest) >= 2:
        opts[rest[0]] = rest[1]
        rest = rest[2:]
    if not argv or "--expect" not in opts or rest:
        print("usage: motion_browser.py SITE_DIR --expect DIR [--shots DIR] [--workers N] "
              "[--engine chromium|firefox]")
        return 2
    site, expect, shots = argv[0], opts["--expect"], opts.get("--shots")
    workers = int(opts.get("--workers", "1"))
    helpers = {"new_page": site_browser.new_page, "goto": site_browser.goto,
               "figure_reports": site_browser.figure_reports, "listed": listed_motions(site),
               "engine": engine}
    c = site_browser.Checks()
    pages = motion_pages(site)
    server, base = site_browser.serve(site)
    with sync_playwright() as p:
        browser = site_browser.launch(p, engine)
        c.check("the site has pages with motions", bool(pages), site)
        c.section("freeze control", freeze_control, c, browser, engine)
        motion_pages_checks(c, browser, base, [(u, u or "/", 1) for u in pages], helpers,
                            expect, shots, workers)
        browser.close()
    server.shutdown()
    print(f"motions: {c.count - c.failed} of {c.count} hold")
    return 1 if c.failed else 0


if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    sys.exit(main(sys.argv[1:]))
