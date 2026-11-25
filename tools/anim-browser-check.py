# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Loads the animated SVGs of the example gallery in a headless Chromium (through Playwright),
# checks that the picture changes with time and that with `prefers-reduced-motion: reduce` the
# poster frame is shown. Needs the `playwright` Python package and a Chromium it can find
# (nothing is installed or downloaded); without them it says so and exits cleanly.
#
# Usage, from the repository root:
#   python3 tools/anim-browser-check.py [EXAMPLES_DIR]
import base64
import os
import sys

try:
    from playwright.sync_api import sync_playwright
except ImportError:
    print("anim-browser-check: the Playwright package is not available; nothing checked")
    sys.exit(0)

NAMES = ["wave", "graph-build"]

DIFF = """async ([a, b]) => {
  const load = src => new Promise((ok, bad) => {
    const i = new Image(); i.onload = () => ok(i); i.onerror = bad; i.src = src; });
  const [x, y] = await Promise.all([load(a), load(b)]);
  const w = Math.min(x.width, y.width), h = Math.min(x.height, y.height);
  const grab = i => { const c = document.createElementNS('http://www.w3.org/1999/xhtml', 'canvas'); c.width = w; c.height = h;
    const g = c.getContext('2d'); g.drawImage(i, 0, 0, w, h); return g.getImageData(0, 0, w, h).data; };
  const p = grab(x), q = grab(y);
  let sum = 0;
  for (let k = 0; k < p.length; k++) sum += Math.abs(p[k] - q[k]);
  return sum / p.length;
}"""


def uri(data):
    return "data:image/png;base64," + base64.b64encode(data).decode()


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "examples")
    failures = 0
    try:
        pw = sync_playwright().start()
        browser = pw.chromium.launch(headless=True)
    except Exception as e:  # no browser found
        print(f"anim-browser-check: no Chromium available ({type(e).__name__}); nothing checked")
        return 0
    try:
        for name in NAMES:
            path = os.path.abspath(os.path.join(root, name + ".svg"))
            poster = os.path.join(root, name + "-poster.png")
            ctx = browser.new_context(viewport={"width": 800, "height": 600})
            page = ctx.new_page()
            page.goto("file://" + path)
            page.evaluate("document.documentElement.pauseAnimations()")
            shots = []
            for t in (0.0, 1.3):
                page.evaluate(f"document.documentElement.setCurrentTime({t})")
                shots.append(page.screenshot())
            ctx.close()
            moved = shots[0] != shots[1]
            rctx = browser.new_context(viewport={"width": 800, "height": 600},
                                       reduced_motion="reduce")
            rpage = rctx.new_page()
            rpage.goto("file://" + path)
            rpage.evaluate("document.documentElement.pauseAnimations()")
            states = []
            for t in (0.0, 1.3):
                rpage.evaluate(f"document.documentElement.setCurrentTime({t})")
                states.append(rpage.screenshot())
            display = rpage.evaluate(
                "[getComputedStyle(document.querySelector('.pilean-motion-poster')).display,"
                " getComputedStyle(document.querySelector('.pilean-motion-live')).display]")
            still = states[0] == states[1]
            box = rpage.evaluate(
                "(() => { const r = document.documentElement.getBoundingClientRect();"
                " return [r.width, r.height]; })()")
            clip = {"x": 0, "y": 0, "width": box[0], "height": box[1]}
            reduced = rpage.screenshot(clip=clip)
            with open(poster, "rb") as f:
                diff = rpage.evaluate(DIFF, [uri(reduced), uri(f.read())])
            rctx.close()
            ok = moved and still and display == ["inline", "none"] and diff < 8
            failures += 0 if ok else 1
            print(f"{name}: frames at 0 s and 1.3 s differ: {moved}; reduced motion: "
                  f".pilean-motion-poster {display[0]}, .pilean-motion-live {display[1]}, "
                  f"picture static: {still}, "
                  f"mean difference from the poster PNG {diff:.2f} of 255 -> "
                  f"{'ok' if ok else 'FAILED'}")
    finally:
        browser.close()
        pw.stop()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
