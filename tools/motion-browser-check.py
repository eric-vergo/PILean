# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Loads the golden motions of plane figures and pictures of panels (with their narrow
# renditions) in a headless Chromium (through Playwright), each standalone SVG file opened
# directly, and checks what a reader sees against what the motion means. The files and the
# expectations come from `lake exe pilean-test --motion-out DIR`; every motion with a `.json` of
# expectations in DIR is checked.
#
# With the clock paused and set (`setCurrentTime`), every `[data-pilean-actor]` anchor is read
# through `getCTM()`:
#   (a) at the middle of each key's rest every actor is where the key's still has it, and every
#       label's or marker's anchor where the motion's plan draws it (0.05 px),
#       and the picture is the key's still SVG up to antialiasing (`UNEXPLAINED`): no pixel is
#       unexplained, a pixel of one picture being unexplained by the other when both of two
#       tests fail: (1) one of its channels lies outside the range of the other's pixels at most
#       one pixel away, widened by 40 levels (`RANGE_WIDEN`); and (2) after a 3 by 3 box blur of
#       both pictures, one of its channels differs from the other's by more than a fifth
#       (`BLUR_RATIO`) of the local contrast, the widest range of a channel over the 5 by 5
#       pixels around it in both pictures. Chromium draws a shape turned into place by `rotate()`
#       a little otherwise than the same shape drawn in place: at the tangents of a circle and
#       along a segment, single pixels up to 57 levels apart (the fixtures in
#       `tools/fixtures/motion-pixels/`), which fail (1) alone; the blur spreads such a pixel over
#       its neighbours, and where (1) fails, correct pictures differ after it by at most 0.11 of
#       the local contrast (measured on 58 renditions of a two-panel motion; the fixtures 0.005).
#       Whatever (1) catches, (2) catches too when a stroke, label, dot or ring is moved by 2
#       pixels or more or is missing: measured at 0.33 of the local contrast or more for a 1 px
#       line in ink or faint grey (light and dark theme, 0.75 to 2 px wide), a label, dots of
#       radius 1 to 2.5 (ink, faint, accent, a #d4d4d8 trail dot, one at 35 % opacity) and dashed
#       rings. What (1) does not see the rule does not see: a difference of less than about 40 to
#       50 levels (a fill at 10 % opacity missing or of another colour; a line of less than 50
#       levels of contrast moved), and most shapes moved by 1 pixel. The anchor checks below are
#       the precise instrument (0.05 px), for the actors' anchors and the upright marks only;
#   (b) at a quarter, a half and three quarters of every turn the actor is on the turn's circle
#       (0.05 px) at the eased fraction of the turn's angle (0.5 degrees): a true arc;
#   (b') at a quarter, a half and three quarters of every slide (of an actor that does nothing
#       else in its step) the actor is on the straight segment between its anchors in the two
#       keys, at the eased fraction (0.05 px); a motion may have no turn or no slide;
#   (c) labels and markers (`[data-pilean-upright]`) are not turned (less than 0.01 degrees),
#       and there are as many of them as the motion declares (none found is a failure);
#   (d) under `prefers-reduced-motion: reduce` the moving picture is not shown, the poster
#       still is, and the page matches the poster key's PNG; switching reduced motion on and off
#       again without seeking shows the picture of the running clock (not a frozen one): it is
#       switched on inside one key's rest and off again for a moment inside a later key's rest
#       that certainly draws another picture (an actor in one and not the other, or
#       moved by more than a pixel; `switch_times`), and the pictures of the two times must
#       differ, or the probe fails as undecided;
#   (e) no console errors;
#   (f) for a picture of panels (its expectations list the panels' boxes and `phase`): at every
#       rest each panel's part of the picture is its part of the composed still (the pixel rule
#       of (a), within the panel's box), and at every rest and at a quarter, a half and three
#       quarters of every move every actor of every panel is where the composed baker has it
#       (0.05 px) at the same clock time: the panels are in phase; and at 60 times through the
#       cycle, with each panel's moving picture shown alone, no pixel of it other than the
#       background's lies outside its own box and the titles' band: nothing leaves its panel
#       while it moves, neither out of the picture nor into another panel.
# Labels and markers that turn (`turning_marks` in the expectations, from the motion's model)
# must have upright groups; a picture without any (only fades, say) has none to find.
# Without seeking, the motion plays: screenshots taken when the running clock reaches two moments
# of different moves (from the expectations) differ.
# Before the motions, the pixel rule is checked on its fixtures (`pixel_rule_checks`): a circle and
# a segment drawn in place and turned into place pass it, and either moved by 2 or 3 pixels fails.
#
# Needs the `playwright` Python package and a browser of the engine that it can find (nothing is
# installed or downloaded); without them it says so and exits cleanly.
#
# Usage, from the repository root:
#   lake exe pilean-test --motion-out DIR
#   python3 tools/motion-browser-check.py DIR [--engine chromium|firefox|webkit]
#
# Engines: Chromium (the default) is the engine the pixel rule's tolerances were measured on and
# the one a continuous-integration gate runs. `--engine firefox` runs the same checks in
# Playwright's Firefox with the same tolerances, which were not measured there: a failure of the
# pixel rule alone in Firefox is to be measured before it is read as a fault, and the fixtures
# need not show Chromium's effect there (it is reported). `--engine webkit` runs the position
# checks in the system's WebKit on macOS (`tools/webkit/webkit_check.py`), not the pixel rule.
import base64
import json
import math
import os
import sys

try:
    from playwright.sync_api import sync_playwright
except ImportError:
    print("motion-browser-check: the Playwright package is not available; nothing checked")
    sys.exit(0)


REST_TOL = 0.05
PHASE_TOL = 0.05
VIEWPORT = {"width": 800, "height": 1000}
RADIUS_TOL = 0.05
ANGLE_TOL = 0.5
UPRIGHT_TOL = 0.01

READ = """async (t) => {
  const svg = document.documentElement;
  svg.setCurrentTime(t);
  await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
  const at = (m, x, y) => [m.a * x + m.c * y + m.e, m.b * x + m.d * y + m.f];
  const actors = [], uprights = [];
  for (const g of svg.querySelectorAll('[data-pilean-actor]')) {
    const [x, y] = g.getAttribute('data-pilean-anchor').split(' ').map(Number);
    actors.push([g.getAttribute('data-pilean-actor'), at(g.getCTM(), x, y)]);
  }
  for (const g of svg.querySelectorAll('[data-pilean-upright]')) {
    const [x, y] = g.getAttribute('data-pilean-upright').split(' ').map(Number);
    const m = g.getCTM();
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
    const c = document.createElementNS('http://www.w3.org/1999/xhtml', 'canvas');
    c.width = w; c.height = h;
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

# The two tests of the pixel rule (see the header): the range widened by RANGE_WIDEN levels, the
# blurred difference above BLUR_RATIO of the local contrast.
RANGE_WIDEN = 40
BLUR_RATIO = 0.2

UNEXPLAINED = """async ([a, b, widen, ratio, shift]) => {
  const load = src => new Promise((ok, bad) => {
    const i = new Image(); i.onload = () => ok(i); i.onerror = bad; i.src = src; });
  const [x, y] = await Promise.all([load(a), load(b)]);
  const w = Math.min(x.width, y.width), h = Math.min(x.height, y.height);
  // the second picture is drawn `shift` pixels to the right over white (0 but in the tests of
  // the rule itself)
  const grab = (i, dx) => {
    const c = document.createElementNS('http://www.w3.org/1999/xhtml', 'canvas');
    c.width = w; c.height = h;
    const g = c.getContext('2d'); g.fillStyle = '#fff'; g.fillRect(0, 0, w, h);
    g.drawImage(i, dx, 0, w, h);
    return g.getImageData(0, 0, w, h).data; };
  const p = grab(x, 0), q = grab(y, shift || 0);
  // each channel of each picture after a 3 by 3 box blur (edges repeated)
  const blur = s => {
    const o = new Float32Array(w * h * 3);
    for (let yy = 0; yy < h; yy++) for (let xx = 0; xx < w; xx++) for (let c = 0; c < 3; c++) {
      let sum = 0;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
        const u = Math.min(w - 1, Math.max(0, xx + dx)), v = Math.min(h - 1, Math.max(0, yy + dy));
        sum += s[4 * (v * w + u) + c];
      }
      o[3 * (yy * w + xx) + c] = sum / 9;
    }
    return o;
  };
  const bp = blur(p), bq = blur(q);
  const blurred = k => {
    let d = 0;
    for (let c = 0; c < 3; c++) d = Math.max(d, Math.abs(bp[3 * k + c] - bq[3 * k + c]));
    return d;
  };
  // the local contrast at a pixel: the widest range of a channel over the 5 by 5 neighbourhood,
  // in both pictures
  const local = (xx, yy) => {
    let d = 0;
    for (let c = 0; c < 3; c++) {
      let lo = 255, hi = 0;
      for (let dy = -2; dy <= 2; dy++) for (let dx = -2; dx <= 2; dx++) {
        const u = xx + dx, v = yy + dy;
        if (u < 0 || v < 0 || u >= w || v >= h) continue;
        for (const s of [p, q]) {
          const z = s[4 * (v * w + u) + c];
          if (z < lo) lo = z;
          if (z > hi) hi = z;
        }
      }
      d = Math.max(d, hi - lo);
    }
    return d;
  };
  // a pixel of s is explained by t when each of its channels lies within the range of t's
  // pixels at most one pixel away, widened by `widen` (an edge moved by less than a pixel stays
  // between its neighbours' colours), or when the blurred pictures differ there by at most
  // `ratio` of the local contrast (a pixel drawn otherwise by the rasteriser, in an outline at
  // the same place); `worst` is the largest such fraction among the pixels the range test does
  // not explain
  let worst = 0;
  const count = (s, t) => {
    let n = 0;
    for (let yy = 0; yy < h; yy++) for (let xx = 0; xx < w; xx++) {
      const k = 4 * (yy * w + xx);
      let ok = true;
      for (let c = 0; c < 3 && ok; c++) {
        let lo = 255, hi = 0;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
          const u = xx + dx, v = yy + dy;
          if (u < 0 || v < 0 || u >= w || v >= h) continue;
          const z = t[4 * (v * w + u) + c];
          if (z < lo) lo = z;
          if (z > hi) hi = z;
        }
        if (s[k + c] < lo - widen || s[k + c] > hi + widen) ok = false;
      }
      if (ok) continue;
      const f = blurred(yy * w + xx) / Math.max(1, local(xx, yy));
      if (f > worst) worst = f;
      if (f > ratio) n++;
    }
    return n;
  };
  return {n: [count(p, q), count(q, p)], worst};
}"""

OUTSIDE = """async ([a, boxes]) => {
  const i = await new Promise((ok, bad) => {
    const x = new Image(); x.onload = () => ok(x); x.onerror = bad; x.src = a; });
  const c = document.createElementNS('http://www.w3.org/1999/xhtml', 'canvas');
  c.width = i.width; c.height = i.height;
  const g = c.getContext('2d'); g.drawImage(i, 0, 0);
  const p = g.getImageData(0, 0, i.width, i.height).data;
  // the background is the colour of the top left pixel, which no panel draws on
  const bg = [p[0], p[1], p[2]];
  let n = 0;
  for (let y = 0; y < i.height; y++) for (let x = 0; x < i.width; x++) {
    const k = 4 * (y * i.width + x);
    const d = Math.abs(p[k] - bg[0]) + Math.abs(p[k + 1] - bg[1]) + Math.abs(p[k + 2] - bg[2]);
    if (d <= 15) continue;
    if (!boxes.some(([bx, by, bw, bh]) => x >= bx && x < bx + bw && y >= by && y < by + bh)) n++;
  }
  return n;
}"""

DIFF = """async ([a, b]) => {
  const load = src => new Promise((ok, bad) => {
    const i = new Image(); i.onload = () => ok(i); i.onerror = bad; i.src = src; });
  const [x, y] = await Promise.all([load(a), load(b)]);
  const w = Math.min(x.width, y.width), h = Math.min(x.height, y.height);
  const grab = i => {
    const c = document.createElementNS('http://www.w3.org/1999/xhtml', 'canvas');
    c.width = w; c.height = h;
    const g = c.getContext('2d'); g.drawImage(i, 0, 0, w, h);
    return g.getImageData(0, 0, w, h).data; };
  const p = grab(x), q = grab(y);
  let sum = 0;
  for (let k = 0; k < p.length; k++) sum += Math.abs(p[k] - q[k]);
  return sum / p.length;
}"""


def unexplained(page, a, b, ratio=BLUR_RATIO, shift=0, raw=False):
    """The number of unexplained pixels of the screenshots `a` and `b` (PNG bytes, or data URIs
    with `raw`) both ways, and the largest blurred difference, as a fraction of the local contrast,
    at a pixel the range test does not explain."""
    if not raw:
        a, b = uri(a), uri(b)
    r = page.evaluate(UNEXPLAINED, [a, b, RANGE_WIDEN, ratio, shift])
    return sum(r["n"]), r["worst"]


def uri(data):
    return "data:image/png;base64," + base64.b64encode(data).decode()


def wrap(deg):
    return (deg + 180) % 360 - 180


def first(actors, ident):
    for name, xy in actors:
        if name == ident:
            return xy
    return None


# How long before the moment of comparison the switch probe shows the picture again, the least
# time it keeps it hidden, and how far from the middle of a rest it may hide it when the
# expectations do not give the rest's ends (seconds of the motion's clock).
SHOW_LEAD = 0.25
MIN_HIDDEN = 0.8
NEAR_REST = 0.25


def rests_differ(a, b):
    """Whether two rests of the expectations certainly draw different pictures: an actor is in one
    and not the other, or an actor's anchor is more than a pixel apart."""
    at_a = {x["id"]: x["at"] for x in a["actors"]}
    at_b = {x["id"]: x["at"] for x in b["actors"]}
    return at_a.keys() != at_b.keys() or any(math.dist(at_a[k], at_b[k]) > 1 for k in at_a)


def rest_window(rest):
    """The part of a rest where the probe may switch: the rest less 0.1 s at each end, from its
    start and end in the expectations, else `NEAR_REST` about its middle."""
    if "from" in rest and rest["until"] - rest["from"] > 0.3:
        return rest["from"] + 0.1, rest["until"] - 0.1
    return rest["t"] - NEAR_REST, rest["t"] + NEAR_REST


def switch_times(spec, start=0.3):
    """The moments of the switch probe, from the expectations, for a clock at `start`: hidden
    inside one key's rest (`rest_window`) and compared inside a later key's rest that certainly
    draws another picture (`rests_differ`; shown again `SHOW_LEAD` before), at least
    `MIN_HIDDEN` later; the probe that is over soonest, as `(window, time to compare at)`, or
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
            if d >= MIN_HIDDEN:
                off = d
            elif (begin + MIN_HIDDEN - lo_b) % cycle <= hi_b - lo_b:
                off = MIN_HIDDEN
            else:
                off = d + cycle
            if best is None or wait + off < best[0]:
                best = (wait + off, (lo_a, hi_a), (begin + off) % cycle)
    return best and best[1:]


def wait_clock(page, t, cycle, early=0.0, late=0.15):
    """Waits until the running clock of the document is between `early` seconds before `t` and
    `late` seconds after it, modulo the cycle, and returns its time then; `None` if it does not
    get there within two cycles."""
    for _ in range(int((2 * cycle + 2) / 0.015)):
        now = page.evaluate("document.documentElement.getCurrentTime()")
        if 0 <= (now - t + early) % cycle <= early + late:
            return now
        page.wait_for_timeout(15)
    return None


def check(browser, root, name):
    with open(os.path.join(root, name + ".json")) as f:
        spec = json.load(f)
    path = os.path.abspath(os.path.join(root, spec["svg"]))
    errors = []
    ctx = browser.new_context(viewport=VIEWPORT)
    page = ctx.new_page()
    page.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    page.on("pageerror", lambda e: errors.append(str(e)))
    page.goto("file://" + path)
    page.evaluate("document.documentElement.pauseAnimations()")
    rest_err = radius_err = angle_err = upright = worst_ratio = 0.0
    rest_pixels = []
    ok = True
    box = page.evaluate(
        "(() => { const r = document.documentElement.getBoundingClientRect();"
        " return [r.width, r.height]; })()")
    clip = {"x": 0, "y": 0, "width": box[0], "height": box[1]}
    uprights_found = set()
    panel_pixels = {}
    for rest in spec["rests"]:
        seen = page.evaluate(READ, rest["t"])
        uprights_found.add(len(seen["uprights"]))
        upright = max([upright] + [abs(a) for a, _ in seen["uprights"]])
        if len(seen["uprights"]) == len(rest["uprights"]):
            for (_, xy), want in zip(seen["uprights"], rest["uprights"]):
                rest_err = max(rest_err, math.dist(xy, want))
        shot = page.screenshot(clip=clip)
        still_page = ctx.new_page()
        still_page.goto("file://" + os.path.abspath(
            os.path.join(root, f"{name}-key{rest['key']}.svg")))
        still = still_page.screenshot(clip=clip)
        still_page.close()
        n, f = unexplained(page, shot, still)
        rest_pixels.append(n)
        worst_ratio = max(worst_ratio, f)
        for panel in spec.get("panels", []):
            x, y, w, h = panel["box"]
            box_clip = {"x": x, "y": y, "width": w, "height": h}
            part = page.screenshot(clip=box_clip)
            still_page = ctx.new_page()
            still_page.goto("file://" + os.path.abspath(
                os.path.join(root, f"{name}-key{rest['key']}.svg")))
            part_still = still_page.screenshot(clip=box_clip)
            still_page.close()
            n, f = unexplained(page, part, part_still)
            worst_ratio = max(worst_ratio, f)
            panel_pixels[panel["id"]] = max(panel_pixels.get(panel["id"], 0), n)
        for a in rest["actors"]:
            xy = first(seen["actors"], a["id"])
            if xy is None:
                ok = False
                print(f"{name}: key {rest['key']}: no element for {a['id']}")
                continue
            rest_err = max(rest_err, math.dist(xy, a["at"]))
    for turn in spec["turns"]:
        c, s = turn["centre"], turn["start"]
        r = math.dist(s, c)
        a0 = math.degrees(math.atan2(s[1] - c[1], s[0] - c[0]))
        for sample in turn["samples"]:
            seen = page.evaluate(READ, sample["t"])
            uprights_found.add(len(seen["uprights"]))
            upright = max([upright] + [abs(a) for a, _ in seen["uprights"]])
            xy = first(seen["actors"], turn["id"])
            if xy is None:
                ok = False
                continue
            radius_err = max(radius_err, abs(math.dist(xy, c) - r))
            if r >= 1:  # an anchor on the centre itself has no angle
                a = math.degrees(math.atan2(xy[1] - c[1], xy[0] - c[0]))
                angle_err = max(angle_err, abs(wrap((a - a0) - turn["sweep"] * sample["f"])))
    # slides: on the straight segment between the actor's anchors in the two keys, at the eased
    # fraction
    slide_err = 0.0
    for sl in spec.get("slides", []):
        a, b = sl["from"], sl["to"]
        for sample in sl["samples"]:
            seen = page.evaluate(READ, sample["t"])
            uprights_found.add(len(seen["uprights"]))
            upright = max([upright] + [abs(x) for x, _ in seen["uprights"]])
            xy = first(seen["actors"], sl["id"])
            if xy is None:
                ok = False
                print(f"{name}: no element for the sliding {sl['id']}")
                continue
            f = sample["f"]
            slide_err = max(slide_err, math.dist(xy, [a[0] + f * (b[0] - a[0]),
                                                       a[1] + f * (b[1] - a[1])]))
    # panels in phase: every actor of every panel where the composed baker has it, at one time
    phase_err = {}
    for sample in spec.get("phase", []):
        seen = page.evaluate(READ, sample["t"])
        if [i for i, _ in seen["actors"]] != [i for i, _ in sample["actors"]]:
            ok = False
            print(f"{name}: at {sample['t']:.3f} s the actors differ from the expected ones")
            continue
        for (ident, xy), (_, want) in zip(seen["actors"], sample["actors"]):
            panel = ident.split("-")[0]
            phase_err[panel] = max(phase_err.get(panel, 0.0), math.dist(xy, want))
    # each panel's moving picture alone (the others hidden) stays in its own box and the titles'
    # band, at 60 times through the cycle
    outside = 0
    if spec.get("panels"):
        band = spec.get("band", 0)
        bands = [[x, y - band, w, band] for x, y, w, h in (p["box"] for p in spec["panels"])]
        for panel in spec["panels"]:
            page.evaluate(
                "(id) => { for (const g of document.querySelectorAll('[data-pilean-panel]'))"
                " g.style.visibility = g.getAttribute('data-pilean-panel') === id ? '' :"
                " 'hidden'; }", panel["id"])
            x, y, w, h = panel["box"]
            for i in range(60):
                page.evaluate(
                    f"document.documentElement.setCurrentTime({spec['cycle'] * i / 60})")
                page.wait_for_timeout(20)
                n = page.evaluate(OUTSIDE, [uri(page.screenshot(clip=clip)),
                                            [[x, y, w, h]] + bands])
                outside = max(outside, n)
        page.evaluate("for (const g of document.querySelectorAll('[data-pilean-panel]'))"
                      " g.style.visibility = ''")
    ctx.close()
    # reduced motion: the still, not the moving picture
    rctx = browser.new_context(viewport=VIEWPORT, reduced_motion="reduce")
    rpage = rctx.new_page()
    rpage.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    rpage.on("pageerror", lambda e: errors.append(str(e)))
    rpage.goto("file://" + path)
    display = rpage.evaluate(
        "[(s => s.visibility + ' ' + s.opacity)("
        "getComputedStyle(document.querySelector('.pilean-motion-live'))),"
        " getComputedStyle(document.querySelector('.pilean-motion-poster')).display]")
    box = rpage.evaluate(
        "(() => { const r = document.documentElement.getBoundingClientRect();"
        " return [r.width, r.height]; })()")
    shot = rpage.screenshot(clip={"x": 0, "y": 0, "width": box[0], "height": box[1]})
    with open(os.path.join(root, spec["poster_png"]), "rb") as f:
        diff = rpage.evaluate(DIFF, [uri(shot), uri(f.read())])
    rctx.close()
    # reduced motion switched on, the clock running on, and off again: the picture shown is the
    # one of the running clock, not one frozen when it was hidden. The moments come from the
    # expectations (`switch_times`): hidden at the middle of one key's rest and shown again for
    # the middle of a later key's rest whose picture certainly differs, so that a frozen picture
    # and a running one cannot look the same
    times = switch_times(spec)
    sctx = browser.new_context(viewport=VIEWPORT)
    spage = sctx.new_page()
    spage.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    spage.goto("file://" + path)
    hidden_at = None
    if times:
        (lo, hi), show_t = times
        hidden_at = wait_clock(spage, lo, spec["cycle"], 0.0, hi - lo)
        spage.emulate_media(reduced_motion="reduce")
        wait_clock(spage, show_t - SHOW_LEAD, spec["cycle"])
        spage.emulate_media(reduced_motion="no-preference")
        wait_clock(spage, show_t, spec["cycle"])
    spage.evaluate("document.documentElement.pauseAnimations()")
    spage.wait_for_timeout(150)
    shown = spage.screenshot(clip=clip)
    now = spage.evaluate("document.documentElement.getCurrentTime()")

    def off_at(t):
        spage.evaluate(f"document.documentElement.setCurrentTime({t})")
        spage.wait_for_timeout(60)
        return spage.evaluate(PIXELS, [uri(shown), uri(spage.screenshot(clip=clip))])
    # the paused clock and the last frame drawn can be a frame or two apart while something
    # moves: the picture shown must match the running clock's near the pause (5 ms steps within
    # 100 ms before it and 50 ms after) better than half as far as the picture of the time it was
    # hidden, which a picture frozen then would match exactly; and the two times must draw
    # different pictures (the control), or the probe could not tell the two apart
    switch = None
    for k in range(31):
        n = off_at(now - 0.1 + 0.005 * k)
        switch = n if switch is None else min(switch, n)
        if switch == 0:
            break
    frozen = off_at(hidden_at) if hidden_at is not None else 0
    switch_ok = frozen > 0 and (switch == 0 or switch * 2 < frozen)
    if frozen == 0:
        print(f"{name}: the switch probe is undecided: the picture at {now:.2f} s (shown again) "
              f"draws the same as at {hidden_at or 0:.2f} s (hidden), so a frozen picture would "
              "pass; the probe's times must be inside rests of keys that differ")
    sctx.close()
    # it plays: no seeking, two moments of the running clock inside different moves (from the
    # expectations' timeline: samples of the first and the last turn or slide, else the first and
    # the last rest), each waited for on the clock, so that a long first hold does not hide it
    times = sorted({sm["t"] for tn in spec["turns"] + spec.get("slides", [])
                    for sm in tn["samples"]})
    if len(times) < 2:
        times = [spec["rests"][0]["t"], spec["rests"][-1]["t"]]
    pctx = browser.new_context(viewport=VIEWPORT)
    ppage = pctx.new_page()
    ppage.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    ppage.goto("file://" + path)

    def at_clock(t):
        """A screenshot when the running clock is within 0.15 s after `t` (modulo the cycle)."""
        now = wait_clock(ppage, t, spec["cycle"])
        return (now, ppage.screenshot()) if now is not None else (None, None)
    t1, s1 = at_clock(times[0])
    t2, s2 = at_clock(times[-1])
    pctx.close()
    plays = t1 is not None and t2 is not None and s1 != s2
    uprights_ok = (uprights_found == {spec["uprights"]}
                   and (spec["uprights"] > 0) == spec["turning_marks"])
    panels_ok = (all(n == 0 for n in panel_pixels.values())
                 and len(panel_pixels) == len(spec.get("panels", []))
                 and all(e <= PHASE_TOL for e in phase_err.values()) and outside == 0
                 and (not spec.get("phase") or len(phase_err) == len(spec.get("panels", []))))
    ok = (ok and rest_err <= REST_TOL and radius_err <= RADIUS_TOL and angle_err <= ANGLE_TOL
          and slide_err <= REST_TOL
          and upright <= UPRIGHT_TOL and uprights_ok and all(n == 0 for n in rest_pixels)
          and display == ["hidden 0", "inline"] and diff < 8 and switch_ok and not errors
          and plays and panels_ok)
    print(f"{name}: rests {rest_err:.2e} px and {rest_pixels} pixels off the stills (worst "
          f"blurred difference {worst_ratio:.3f} of the local contrast), "
          f"arcs {radius_err:.2e} px and {angle_err:.2e} deg over {len(spec['turns'])} turns, "
          f"slides {slide_err:.2e} px over {len(spec.get('slides', []))}, "
          f"uprights {sorted(uprights_found)} "
          f"of {spec['uprights']} found, turned {upright:.2e} deg; reduced motion: live "
          f"{display[0]}, poster {display[1]}, {diff:.2f} of 255 from the poster PNG, switched "
          f"off again {switch} pixels off the clock ({frozen} off the time it was hidden); "
          f"plays ({t1 or 0:.2f} s, {t2 or 0:.2f} s): {plays}; "
          f"console errors: {len(errors)}"
          + (f"; panels: pixels off their stills {panel_pixels}, in phase within "
             f"{ {k: float(f'{v:.2e}') for k, v in phase_err.items()} } px over "
             f"{len(spec.get('phase', []))} times, {outside} pixels outside the panels at 60 "
             f"times" if spec.get("panels") else "")
          + f" -> {'ok' if ok else 'FAILED'}")
    for e in errors:
        print(f"  console: {e}")
    return ok


FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures", "motion-pixels")


def pixel_rule_checks(browser, engine="chromium"):
    """The pixel rule on its fixtures: each pair of a shape drawn in place and the same shape
    turned into place by `rotate()` (a circle, a horizontal segment), which Chromium draws up to
    57 levels apart at single pixels (which the range test alone does not explain, as it must
    find for the fixture to test anything), must have no unexplained pixel; the picture in place
    against itself moved by 2 and by 3 pixels must have some (the rule catches a shape moved so
    far); moved by 1 pixel is reported, not required. Returns whether all hold."""
    page = browser.new_page(viewport={"width": 340, "height": 700})
    ok = True
    for stem in ["circle", "segment"]:
        shots = []
        for f in [f"{stem}-still.svg", f"{stem}-turned.svg"]:
            page.goto("file://" + os.path.join(FIXTURES, f))
            shots.append(uri(page.screenshot()))
        page.goto("about:blank")
        turned, worst = unexplained(page, shots[0], shots[1], raw=True)
        alone, _ = unexplained(page, shots[0], shots[1], ratio=-1, raw=True)
        moved = {d: unexplained(page, shots[0], shots[0], shift=d, raw=True)[0] for d in (1, 2, 3)}
        # the fixture must show the effect the rule allows for, or it tests nothing; the effect
        # is Chromium's, so another engine that draws both alike only reports it
        shown = alone > 0 or engine != "chromium"
        good = turned == 0 and shown and moved[2] > 0 and moved[3] > 0
        ok = ok and good
        print(f"pixel rule, {stem}: turned into place {turned} unexplained pixels (the range test "
              f"alone: {alone}; largest blurred difference there {worst:.3f} of the local "
              f"contrast, the rule allows {BLUR_RATIO}); moved by 1, 2, 3 px: {moved[1]}, "
              f"{moved[2]}, {moved[3]} -> "
              f"{'ok' if good else 'FAILED'}")
    page.close()
    return ok


def main():
    args = sys.argv[1:]
    engine = "chromium"
    if "--engine" in args:
        i = args.index("--engine")
        engine = args[i + 1]
        del args[i:i + 2]
    if len(args) != 1 or engine not in ("chromium", "firefox", "webkit"):
        print("usage: python3 tools/motion-browser-check.py DIR [--engine chromium|firefox|webkit] "
              "(DIR from `lake exe pilean-test --motion-out DIR`)")
        return 2
    root = args[0]
    if engine == "webkit":
        # the position checks in the system's WebKit, through the optional macOS runner
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "webkit"))
        import webkit_check
        return webkit_check.main([root])
    try:
        pw = sync_playwright().start()
        browser = getattr(pw, engine).launch(headless=True)
    except Exception as e:  # no browser found
        print(f"motion-browser-check: no {engine} available ({type(e).__name__}); nothing checked")
        return 0
    try:
        names = sorted(f[:-5] for f in os.listdir(root) if f.endswith(".json"))
        failures = 0 if pixel_rule_checks(browser, engine) else 1
        failures += sum(0 if check(browser, root, name) else 1 for name in names)
        if not names:
            print(f"motion-browser-check: no motions in {root}")
            failures = 1
    finally:
        browser.close()
        pw.stop()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
