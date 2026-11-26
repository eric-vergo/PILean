# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Loads the golden motions of plane figures in a headless Chromium (through Playwright), each
# standalone SVG file opened directly, and checks what a reader sees against what the motion
# means. The files and the expectations come from `lake exe pilean-test --motion-out DIR`; every
# motion with a `.json` of expectations in DIR is checked.
#
# With the clock paused and set (`setCurrentTime`), every `[data-pilean-actor]` anchor is read
# through `getCTM()`:
#   (a) at the middle of each key's rest every actor is where the key's still has it, and every
#       label's or marker's anchor where the motion's plan draws it (0.05 px),
#       and the picture is the key's still SVG up to antialiasing: every channel of every pixel
#       of each lies within the range of the other's pixels at most one pixel away, widened by
#       40 (a circle turned by 72 degrees is rasterised a little otherwise than the still's own
#       circle, along its outline);
#   (b) at a quarter, a half and three quarters of every turn the actor is on the turn's circle
#       (0.05 px) at the eased fraction of the turn's angle (0.5 degrees): a true arc;
#   (c) labels and markers (`[data-pilean-upright]`) are not turned (less than 0.01 degrees),
#       and there are as many of them as the motion declares (none found is a failure);
#   (d) under `prefers-reduced-motion: reduce` the moving picture is not shown, the poster
#       still is, and the page matches the poster key's PNG; switching reduced motion on and off
#       again without seeking shows the picture of the running clock (not a frozen one);
#   (e) no console errors.
# Without seeking, the motion plays: two screenshots at different `getCurrentTime()` differ.
#
# Needs the `playwright` Python package and a Chromium it can find (nothing is installed or
# downloaded); without them it says so and exits cleanly.
#
# Usage, from the repository root:
#   lake exe pilean-test --motion-out DIR
#   python3 tools/motion-browser-check.py DIR
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

UNEXPLAINED = """async ([a, b]) => {
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
  // a pixel of s is explained by t when each of its channels lies within the range of t's
  // pixels at most one pixel away, widened by 40: an edge moved by less than a pixel stays
  // between its neighbours' colours
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
        if (s[k + c] < lo - 40 || s[k + c] > hi + 40) ok = false;
      }
      if (!ok) n++;
    }
    return n;
  };
  return [count(p, q), count(q, p)];
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


def uri(data):
    return "data:image/png;base64," + base64.b64encode(data).decode()


def wrap(deg):
    return (deg + 180) % 360 - 180


def first(actors, ident):
    for name, xy in actors:
        if name == ident:
            return xy
    return None


def check(browser, root, name):
    with open(os.path.join(root, name + ".json")) as f:
        spec = json.load(f)
    path = os.path.abspath(os.path.join(root, spec["svg"]))
    errors = []
    ctx = browser.new_context(viewport={"width": 800, "height": 700})
    page = ctx.new_page()
    page.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    page.on("pageerror", lambda e: errors.append(str(e)))
    page.goto("file://" + path)
    page.evaluate("document.documentElement.pauseAnimations()")
    rest_err = radius_err = angle_err = upright = 0.0
    rest_pixels = []
    ok = True
    box = page.evaluate(
        "(() => { const r = document.documentElement.getBoundingClientRect();"
        " return [r.width, r.height]; })()")
    clip = {"x": 0, "y": 0, "width": box[0], "height": box[1]}
    uprights_found = set()
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
        rest_pixels.append(sum(page.evaluate(UNEXPLAINED, [uri(shot), uri(still)])))
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
    ctx.close()
    # reduced motion: the still, not the moving picture
    rctx = browser.new_context(viewport={"width": 800, "height": 700}, reduced_motion="reduce")
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
    # one of the running clock, not one frozen when it was hidden
    sctx = browser.new_context(viewport={"width": 800, "height": 700})
    spage = sctx.new_page()
    spage.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    spage.goto("file://" + path)
    spage.wait_for_timeout(300)
    hidden_at = spage.evaluate("document.documentElement.getCurrentTime()")
    spage.emulate_media(reduced_motion="reduce")
    spage.wait_for_timeout(1500)
    spage.emulate_media(reduced_motion="no-preference")
    spage.wait_for_timeout(100)
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
    # hidden, which a picture frozen then would match exactly
    switch = None
    for k in range(31):
        n = off_at(now - 0.1 + 0.005 * k)
        switch = n if switch is None else min(switch, n)
        if switch == 0:
            break
    frozen = off_at(hidden_at)
    switch_ok = switch == 0 or switch * 2 < frozen
    sctx.close()
    # it plays: no seeking, two moments of the running clock
    pctx = browser.new_context(viewport={"width": 800, "height": 700})
    ppage = pctx.new_page()
    ppage.on("console", lambda m: errors.append(m.text) if m.type == "error" else None)
    ppage.goto("file://" + path)
    ppage.wait_for_timeout(600)
    t1 = ppage.evaluate("document.documentElement.getCurrentTime()")
    s1 = ppage.screenshot()
    ppage.wait_for_timeout(1200)
    t2 = ppage.evaluate("document.documentElement.getCurrentTime()")
    s2 = ppage.screenshot()
    pctx.close()
    plays = t2 > t1 and s1 != s2
    uprights_ok = uprights_found == {spec["uprights"]} and spec["uprights"] > 0
    ok = (ok and rest_err <= REST_TOL and radius_err <= RADIUS_TOL and angle_err <= ANGLE_TOL
          and upright <= UPRIGHT_TOL and uprights_ok and all(n == 0 for n in rest_pixels)
          and display == ["hidden 0", "inline"] and diff < 8 and switch_ok and not errors
          and plays)
    print(f"{name}: rests {rest_err:.2e} px and {rest_pixels} pixels off the stills, "
          f"arcs {radius_err:.2e} px and {angle_err:.2e} deg, uprights {sorted(uprights_found)} "
          f"of {spec['uprights']} found, turned {upright:.2e} deg; reduced motion: live "
          f"{display[0]}, poster {display[1]}, {diff:.2f} of 255 from the poster PNG, switched "
          f"off again {switch} pixels off the clock ({frozen} off the time it was hidden); "
          f"plays ({t1:.2f} s, {t2:.2f} s): {plays}; "
          f"console errors: {len(errors)} -> {'ok' if ok else 'FAILED'}")
    for e in errors:
        print(f"  console: {e}")
    return ok


def main():
    if len(sys.argv) != 2:
        print("usage: python3 tools/motion-browser-check.py DIR (from `lake exe pilean-test "
              "--motion-out DIR`)")
        return 2
    root = sys.argv[1]
    try:
        pw = sync_playwright().start()
        browser = pw.chromium.launch(headless=True)
    except Exception as e:  # no browser found
        print(f"motion-browser-check: no Chromium available ({type(e).__name__}); nothing checked")
        return 0
    try:
        names = sorted(f[:-5] for f in os.listdir(root) if f.endswith(".json"))
        failures = sum(0 if check(browser, root, name) else 1 for name in names)
        if not names:
            print(f"motion-browser-check: no motions in {root}")
            failures = 1
    finally:
        browser.close()
        pw.stop()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
