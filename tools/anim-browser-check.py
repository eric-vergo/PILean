# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Loads the animated SVGs of the example gallery in a headless Chromium (through Playwright),
# checks that the picture changes with time, that with `prefers-reduced-motion: reduce` the
# poster frame is shown, and that switching reduced motion off again shows the running picture.
# Needs the `playwright` Python package and a Chromium it can find (nothing is installed or
# downloaded); without them it says so and exits cleanly.
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
                rpage.wait_for_timeout(150)
                states.append(rpage.screenshot())
            display = rpage.evaluate(
                "[getComputedStyle(document.querySelector('.pilean-motion-poster')).display,"
                " (s => s.visibility + ' ' + s.opacity)("
                "getComputedStyle(document.querySelector('.pilean-motion-live')))]")
            # no pixel whose colour differs by more than 60 in the sum of its channels
            still = rpage.evaluate(PIXELS, [uri(states[0]), uri(states[1])]) == 0
            box = rpage.evaluate(
                "(() => { const r = document.documentElement.getBoundingClientRect();"
                " return [r.width, r.height]; })()")
            clip = {"x": 0, "y": 0, "width": box[0], "height": box[1]}
            reduced = rpage.screenshot(clip=clip)
            with open(poster, "rb") as f:
                diff = rpage.evaluate(DIFF, [uri(reduced), uri(f.read())])
            rctx.close()
            # reduced motion on and off again, the clock running: the picture shown is the
            # running clock's, not one frozen while it was hidden
            sctx = browser.new_context(viewport={"width": 800, "height": 600})
            spage = sctx.new_page()
            spage.goto("file://" + path)
            spage.wait_for_timeout(200)
            spage.emulate_media(reduced_motion="reduce")
            spage.wait_for_timeout(700)
            spage.emulate_media(reduced_motion="no-preference")
            spage.wait_for_timeout(100)
            spage.evaluate("document.documentElement.pauseAnimations()")
            spage.wait_for_timeout(150)
            shown = spage.screenshot(clip=clip)
            now = spage.evaluate("document.documentElement.getCurrentTime()")
            # the paused clock and the last frame drawn can be a frame or two apart: the picture
            # shown must be one of the running clock's within 50 ms
            switch = False
            for dt in (0, -0.01, 0.01, -0.02, 0.02, -0.03, 0.03, -0.05, 0.05):
                spage.evaluate(f"document.documentElement.setCurrentTime({now + dt})")
                spage.wait_for_timeout(100)
                if spage.evaluate(PIXELS, [uri(shown), uri(spage.screenshot(clip=clip))]) == 0:
                    switch = True
                    break
            sctx.close()
            ok = moved and still and display == ["inline", "hidden 0"] and diff < 8 and switch
            failures += 0 if ok else 1
            print(f"{name}: frames at 0 s and 1.3 s differ: {moved}; reduced motion: "
                  f".pilean-motion-poster {display[0]}, .pilean-motion-live "
                  f"{display[1]}, picture static: {still}, switched off again shows the "
                  f"running clock: {switch}, "
                  f"mean difference from the poster PNG {diff:.2f} of 255 -> "
                  f"{'ok' if ok else 'FAILED'}")
    finally:
        browser.close()
        pw.stop()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
