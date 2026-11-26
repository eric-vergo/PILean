# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
"""The browser checks of motions shown in a page, run by `browser_check.py`.

`motion_checks` checks the motions of one page of a site (the Blueprint example's "Motion" page,
the Manual example's), served under the strict content policy of `browser_check.py`:

* with the expectations `ExampleTest --motion-out DIR` writes (the Blueprint example only): with
  the clock paused and set, every actor of the page's moving picture is where its key still has
  it at every rest (0.05 px), on its circle at a quarter, a half and three quarters of every turn
  (0.05 px, a true arc) at the eased angle (0.5 degrees), every label and marker upright (0.01
  degrees), and every panel of a picture of panels in phase with the others (0.05 px);
* the wide rendition is shown at 1440 px and the narrow one at 360 px, the other hidden and
  taking no space;
* switching the theme while the picture moves recolours it, and it keeps moving;
* each way of turning motion off (the system's reduced motion, `data-motion="reduce"` on the
  root, the Blueprint's switch, print) hides the moving picture and shows the stills with their
  captions; hovering and focusing the picture show the poster key's still in the picture's own
  box, nothing around it moving; after each of them ends, the moving picture follows its clock
  again without being sought (the regression test for a picture frozen after it was hidden; the
  check is shown to notice a picture hidden with `display: none`);
* the captions are in the accessibility tree while the stills are hidden, and nothing is
  announced (no live region changes);
* every id of the page once, and no `data-pilean-actor` in two pictures;
* the Blueprint's caption link leads to the motion switch;
* no console error.
"""

import base64
import json
import math
import os

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
  const imgs = [...keys.querySelectorAll('img')].filter(i => i.offsetParent !== null);
  const r = stage.getBoundingClientRect();
  return {live: getComputedStyle(svg).visibility,
          stage: getComputedStyle(stage).visibility, stageDisplay: getComputedStyle(stage).display,
          still: getComputedStyle(still).opacity,
          keys: keys.getBoundingClientRect().height, keysDisplay: getComputedStyle(keys).display,
          shownStills: imgs.length,
          loaded: imgs.every(i => i.complete && i.naturalWidth > 0),
          figure: m.closest('figure').getBoundingClientRect().height,
          stageBox: [r.width, r.height]};
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


def state_checks(c, browser, base, url, sid, label, helpers, blueprint, control=False):
    """Each way of turning motion off, and hover and focus, on the moving picture `sid`."""
    new_page, goto = helpers["new_page"], helpers["goto"]
    states = ["data-motion"] if control else ["reduced motion", "data-motion", "hover", "focus"]
    cmp = browser.new_page()
    if blueprint and not control:
        states.append("switch")
    for state in states:
        ctx, page = new_page(browser, viewport={"width": 1440, "height": 900})
        errors = []
        page.on("console", lambda m: errors.append(m.text) if console_error(m) else None)
        goto(page, base + url)
        if control:
            page.add_style_tag(content='html[data-motion="reduce"] .pilean-motion-stage'
                                       '{display:none !important}')
        page.locator(f"[id='{sid}']").scroll_into_view_if_needed()
        page.wait_for_timeout(300)
        before = page.evaluate(STATE, sid)
        verdict = None
        for hold in (1300, 2100, 3700):
            hidden_at = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()",
                                      sid)
            stage = page.locator(f"[id='{sid}']").locator("xpath=ancestor::div[1]")
            if state == "reduced motion":
                page.emulate_media(reduced_motion="reduce")
            elif state == "data-motion":
                page.evaluate("document.documentElement.setAttribute('data-motion', 'reduce')")
            elif state == "switch":
                page.locator("#bp-motion button[data-motion-choice=off]").click()
                page.locator(f"[id='{sid}']").scroll_into_view_if_needed()
            elif state == "hover":
                stage.hover()
            else:
                stage.focus()
            page.wait_for_timeout(hold)
            during = page.evaluate(STATE, sid)
            off = state in ("reduced motion", "data-motion", "switch")
            if state == "reduced motion":
                page.emulate_media(reduced_motion="no-preference")
            elif state == "data-motion":
                page.evaluate("document.documentElement.removeAttribute('data-motion')")
            elif state == "switch":
                page.locator("#bp-motion button[data-motion-choice=on]").click()
            elif state == "hover":
                page.mouse.move(2, 2)
            else:
                page.evaluate("document.activeElement.blur()")
            after = page.evaluate(STATE, sid)
            verdict, numbers = follows_clock(page, sid, hidden_at, cmp)
            if verdict is not None:
                break
        if control:
            c.check(f"{label}: the freeze check notices a picture hidden with display: none",
                    verdict is False, str(numbers))
            ctx.close()
            cmp.close()
            return
        if off:
            shown = during["live"] == "hidden" and during["keysDisplay"] == "grid" and \
                during["keys"] > 20 and during["shownStills"] > 0 and during["loaded"]
            what = "hides the moving picture and shows the stills with their captions"
        else:
            shown = during["live"] == "hidden" and during["still"] == "1" and \
                during["keys"] <= 1 and abs(during["figure"] - before["figure"]) < 0.5 and \
                during["stageBox"] == before["stageBox"]
            what = "shows the poster's still in the picture's own box, nothing moving around it"
        c.check(f"{label}: {state} {what}", shown, f"{before} -> {during}")
        c.check(f"{label}: after {state} the picture is back and follows its clock without "
                "seeking", after["live"] == "visible" and after["stage"] == "visible" and
                verdict is True, f"{after['live']} {numbers}")
        c.check(f"{label}: {state}: no console error", not errors, str(errors[:2]))
        ctx.close()
    cmp.close()


def motion_checks(c, browser, base, url, label, helpers, expect=None, blueprint=True,
                  shots=None):
    """The checks of the module docstring on the page `url` of the site at `base`."""
    new_page, goto, reports = helpers["new_page"], helpers["goto"], helpers["figure_reports"]
    ctx, page = new_page(browser, viewport={"width": 1440, "height": 900})
    errors = []
    page.on("console", lambda m: errors.append(m.text) if console_error(m) else None)
    goto(page, base + url)
    sids = motion_ids(page)
    c.check(f"{label}: the page shows its motions inline", len(sids) >= 2, str(sids))
    # positions, from the expectations
    if expect:
        for sid in sids:
            for suffix, vw in [("", 1440), ("-narrow", 360)]:
                name = file_of(page, sid) + suffix
                path = os.path.join(expect, name + ".json")
                if not os.path.exists(path):
                    continue
                with open(path) as f:
                    spec = json.load(f)
                vctx, vpage = new_page(browser, viewport={"width": vw, "height": 900})
                goto(vpage, base + url)
                target = sid if not suffix else sid[:-len("-mw")] + "-mn"
                position_checks(c, vpage, target, spec, f"{label} {name} ({vw} px)")
                vctx.close()
    # it moves by itself
    # sampled for longer than a cycle of each, all at once
    seen = {sid: [] for sid in sids}
    for _ in range(24):
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
    snap = page.locator(".pilean-motion").first.aria_snapshot()
    hidden = page.evaluate("""() => document.querySelector('.pilean-motion-keys')
      .getBoundingClientRect().height""")
    c.check(f"{label}: the stills' captions are in the accessibility tree while hidden",
            hidden <= 1 and "Step 1 of" in snap and "listitem" in snap, snap[:300])
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
    s1 = shot(page, sid)
    page.wait_for_timeout(600)
    s2 = shot(page, sid)
    t1 = page.evaluate("(sid) => document.getElementById(sid).getCurrentTime()", sid)
    c.check(f"{label}: switching the theme while it moves recolours the picture, which moves on",
            dark[1] == rgb(pair) and light[1] != dark[1] and t1 > t0 and s1 != s2,
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
    c.check(f"{label}: printed, every motion shows its stills and not its moving picture",
            all(p["stageDisplay"] == "none" and p["keysDisplay"] == "grid" and p["keys"] > 20
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
        c.check(f"{label} {width} px: the {'wide' if shown == 'mw' else 'narrow'} rendition is "
                "shown and the other takes no space",
                bool(res) and all(r[0] == "visible" and r[1] == "hidden" and r[2] == "absolute"
                                  and r[3] < 1 for r in res), str(res))
        if shots:
            page.screenshot(path=f"{shots}/motion-{width}.png", full_page=True)
        ctx.close()
    for width in [360, 768, 1440]:
        ctx, page = new_page(browser, viewport={"width": width, "height": 900})
        goto(page, base + url)
        wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
        c.check(f"{label} {width} px: no sideways scrolling", wide <= 0, f"{wide} px")
        ctx.close()
    # states, with the freeze check and its control
    target = next((s for s in narrow_sids), sids[0])
    state_checks(c, browser, base, url, target, label, helpers, blueprint)
    state_checks(c, browser, base, url, target, label, helpers, blueprint, control=True)


def page_has_narrow(browser, base, url, sid, helpers):
    ctx, page = helpers["new_page"](browser, viewport={"width": 800, "height": 600})
    helpers["goto"](page, base + url)
    has = page.evaluate("(sid) => !!document.getElementById(sid.slice(0, -3) + '-mn')", sid)
    ctx.close()
    return has
