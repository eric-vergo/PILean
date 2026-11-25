# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Loads the golden motions of plane figures in a headless Chromium (through Playwright), each
# standalone SVG file opened directly, and checks what a reader sees against what the motion
# means. The files and the expectations come from `lake exe pilean-test --motion-out DIR`.
#
# With the clock paused and set (`setCurrentTime`), every `[data-pilean-actor]` anchor is read
# through `getCTM()`:
#   (a) at the middle of each key's rest every actor is where the key's still has it (0.05 px);
#   (b) at a quarter, a half and three quarters of every turn the actor is on the turn's circle
#       (0.05 px) at the eased fraction of the turn's angle (0.5 degrees): a true arc;
#   (c) labels and markers (`[data-pilean-upright]`) are not turned (less than 0.01 degrees);
#   (d) under `prefers-reduced-motion: reduce` the moving picture is not rendered, the poster
#       still is, and the page matches the poster key's PNG;
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

NAMES = ["motion-turn", "motion-two-centres"]

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
    const m = g.getCTM();
    uprights.push(Math.atan2(m.b, m.a) * 180 / Math.PI);
  }
  return {time: svg.getCurrentTime(), actors, uprights};
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
    ok = True
    for rest in spec["rests"]:
        seen = page.evaluate(READ, rest["t"])
        upright = max([upright] + [abs(a) for a in seen["uprights"]])
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
            upright = max([upright] + [abs(a) for a in seen["uprights"]])
            xy = first(seen["actors"], turn["id"])
            if xy is None:
                ok = False
                continue
            radius_err = max(radius_err, abs(math.dist(xy, c) - r))
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
        "[getComputedStyle(document.querySelector('.pilean-motion-live')).display,"
        " getComputedStyle(document.querySelector('.pilean-motion-poster')).display]")
    box = rpage.evaluate(
        "(() => { const r = document.documentElement.getBoundingClientRect();"
        " return [r.width, r.height]; })()")
    shot = rpage.screenshot(clip={"x": 0, "y": 0, "width": box[0], "height": box[1]})
    with open(os.path.join(root, spec["poster_png"]), "rb") as f:
        diff = rpage.evaluate(DIFF, [uri(shot), uri(f.read())])
    rctx.close()
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
    ok = (ok and rest_err <= REST_TOL and radius_err <= RADIUS_TOL and angle_err <= ANGLE_TOL
          and upright <= UPRIGHT_TOL and display == ["none", "inline"] and diff < 8
          and not errors and plays)
    print(f"{name}: rests {rest_err:.2e} px, arcs {radius_err:.2e} px and {angle_err:.2e} deg, "
          f"uprights {upright:.2e} deg; reduced motion: live {display[0]}, poster {display[1]}, "
          f"{diff:.2f} of 255 from the poster PNG; plays ({t1:.2f} s, {t2:.2f} s): {plays}; "
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
        failures = sum(0 if check(browser, root, name) else 1 for name in NAMES)
    finally:
        browser.close()
        pw.stop()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
