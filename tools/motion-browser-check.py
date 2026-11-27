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
#   (a) at the middle of each key's rest every actor is where the key's still has it (again one
#       cycle later, in the second loop: the anchors; turns, slides and phase likewise), and every
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
#   (f) at every sample of every appearance and disappearance (the expectations' `opacities`: 0.05 s
#       before its window, in its middle and 0.05 s after, the window in a step, through a whole
#       step or in a rest), in both loops, the nth layer of its actor (the nth element with that
#       `data-pilean-actor`) is at the expected opacity, within 0.02 (`OPACITY_TOL`): the opacity
#       read is the product of the computed opacity of the layer and of each ancestor up to the
#       root, the seam's group included (`OPACITY`). Chromium, Firefox and WebKit all put the value
#       of a SMIL animation of the `opacity` attribute in the computed style; that it is what is
#       drawn is measured from the pixels in the first loop (`drawn_opacity`: the picture, the
#       picture without the layer and with it opaque, the median of (shown - without) / (opaque -
#       without) over the pixels where the last two differ by 64 levels or more), within 0.03
#       (`DRAWN_TOL`: 8-bit channels over 64 levels move in steps of 1/64). Measured on the golden
#       motions (108 samples, 54 measured from the pixels): read against expected at most 8e-6 in
#       Chromium, 0 in Firefox and 3e-6 in WebKit (the writer rounds opacities to 4 decimals and
#       splines to 6); drawn against expected at most 0.006 in Chromium and Firefox and 0.002 in
#       WebKit (measured once, with a snapshot of the `WKWebView`, which `tools/webkit/` does not
#       take). Every listed sample must be read (none missing), and the line says how many were;
#   (g) for a picture of panels (its expectations list the panels' boxes and `phase`): at every
#       rest each panel's part of the picture is its part of the composed still (the pixel rule
#       of (a), within the panel's box), and at every rest and at a quarter, a half and three
#       quarters of every move every actor of every panel is where the composed baker has it
#       (0.05 px) at the same clock time: the panels are in phase; and at 60 times through the
#       cycle, with each panel's moving picture shown alone, no pixel of it other than the
#       background's lies outside its own box and the titles' band: nothing leaves its panel
#       while it moves, neither out of the picture nor into another panel.
# The expectations must be in format 3 (`FORMAT`); another format fails, saying which was found.
# Every key has a rest, a key that is not a still (`still` false) included: it takes part in every
# check above, and DIR has its picture `<name>-key{k}.svg` like every key's. A rest is checked at
# the part of it in which its key is shown still (`from` to `until`, after the rest's fades, `t`
# its middle); the switch probe uses only rests whose part is longer than 0.3 s.
# Labels and markers that turn (`turning_marks` in the expectations, from the motion's model)
# must have upright groups; a picture without any (only fades, say) has none to find.
# Without seeking, the motion plays: screenshots taken when the running clock reaches two moments
# of different moves (from the expectations) differ.
# Before the motions, the pixel rule is checked on its fixtures (`pixel_rule_checks`): a circle and
# a segment drawn in place and turned into place pass it, and either moved by 2 or 3 pixels fails.
# After the motions, the opacity check is shown to catch a mark whose fade never starts
# (`opacity_mutation`): in the first motion that lists opacities, the opacity animation of the
# group nearest the first entry's layer is held at 0 in the page before seeking, and samples must
# be found off ("caught"); the last line gives the motions, the opacity samples asserted and the
# failures.
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
# Playwright's Firefox (Firefox 159), with the same tolerances, measured there too: on the golden
# motions and both examples' motions no rest pixel is unexplained and the largest blurred
# difference where the range test fails is 0.000 of the local contrast; on the fixtures Firefox
# draws the circle turned into place as it draws it in place (the range test alone finds 0
# pixels, where Chromium finds 5, which is reported, not required) and the segment as Chromium
# does (19 pixels, 0.005), and a shape moved by 2 or 3 px is caught. `--engine webkit` runs the
# position checks in the system's WebKit on macOS (`tools/webkit/webkit_check.py`), not the pixel
# rule, and the opacity samples of (f) without their measure from the pixels.
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
# the opacity of a layer read from the computed style, and as measured from its pixels (see the
# header)
OPACITY_TOL = 0.02
DRAWN_TOL = 0.03

READ ="""async (t) => {
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


# The opacity a reader sees of an actor's layer: the product of the computed opacity of the nth
# element with that `data-pilean-actor` and of each of its ancestors up to the root (Chromium and
# Firefox put the value of a SMIL animation of the `opacity` attribute in the computed style;
# `drawn_opacity` checks that it is what is drawn); `null` when there is no such element.
OPACITY = """async ([t, id, nth]) => {
  const svg = document.documentElement;
  svg.setCurrentTime(t);
  await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r)));
  const el = [...svg.querySelectorAll('[data-pilean-actor]')]
    .filter(e => e.getAttribute('data-pilean-actor') === id)[nth];
  if (!el) return null;
  let o = 1;
  for (let e = el; e; e = e.parentElement) {
    o *= parseFloat(getComputedStyle(e).opacity);
    if (e === svg) break;
  }
  return o;
}"""

# What `drawn_opacity` does to the nth layer of an actor between its screenshots: `hide` it
# (`visibility`), make it `opaque` (every opacity animation of it and its ancestors held at 1),
# `restore` both; `fade-never-starts` holds the opacity animation of the group nearest the layer
# at 0 (the mutation of `opacity_mutation`). Returns whether the layer was found.
LAYER = """([id, nth, what]) => {
  const svg = document.documentElement;
  const el = [...svg.querySelectorAll('[data-pilean-actor]')]
    .filter(e => e.getAttribute('data-pilean-actor') === id)[nth];
  if (!el) return false;
  const fades = [];
  for (let e = el; e && e !== svg; e = e.parentElement)
    for (const c of e.children)
      if (c.localName === 'animate' && c.getAttribute('attributeName') === 'opacity') fades.push(c);
  const held = v => a => {
    if (!a.hasAttribute('data-kept')) a.setAttribute('data-kept', a.getAttribute('values'));
    a.setAttribute('values', a.getAttribute('values').split(';').map(() => v).join(';'));
  };
  if (what === 'hide') el.style.visibility = 'hidden';
  else if (what === 'opaque') { el.style.visibility = ''; fades.forEach(held('1')); }
  else if (what === 'fade-never-starts') { if (!fades.length) return false; held('0')(fades[0]); }
  else if (what === 'window-shifted') {
    // every value one boundary later: the fade runs one interval of the clock after its window
    if (!fades.length) return false;
    const v = fades[0].getAttribute('values').split(';');
    fades[0].setAttribute('values', [v[0], ...v.slice(0, -1)].join(';'));
  }
  else {
    el.style.visibility = '';
    for (const a of fades) if (a.hasAttribute('data-kept')) {
      a.setAttribute('values', a.getAttribute('data-kept')); a.removeAttribute('data-kept'); }
  }
  return true;
}"""

# The opacity drawn, from three screenshots of one time: the picture `s`, the picture without
# the layer `h` and with the layer opaque `f`. Where some channel of `f` and `h` differs by 64
# levels or more (the layer's own pixels, away from antialiased edges), (s - h) / (f - h) in that
# channel is the layer's opacity; the median over those pixels, and how many there were.
RATIO = """async ([a, b, c]) => {
  const load = src => new Promise((ok, bad) => {
    const i = new Image(); i.onload = () => ok(i); i.onerror = bad; i.src = src; });
  const imgs = await Promise.all([load(a), load(b), load(c)]);
  const w = imgs[0].width, h = imgs[0].height;
  const [s, hh, f] = imgs.map(i => {
    const cv = document.createElementNS('http://www.w3.org/1999/xhtml', 'canvas');
    cv.width = w; cv.height = h;
    const g = cv.getContext('2d'); g.drawImage(i, 0, 0, w, h);
    return g.getImageData(0, 0, w, h).data; });
  const r = [];
  for (let k = 0; k < s.length; k += 4) {
    let best = 0, ch = 0;
    for (let q = 0; q < 3; q++) {
      const d = Math.abs(f[k + q] - hh[k + q]);
      if (d > best) { best = d; ch = q; }
    }
    if (best >= 64) r.push((s[k + ch] - hh[k + ch]) / (f[k + ch] - hh[k + ch]));
  }
  r.sort((x, y) => x - y);
  return [r.length ? r[r.length >> 1] : null, r.length];
}"""


def drawn_opacity(page, clip, t, ident, nth):
    """The opacity of the nth layer of the actor `ident` as drawn at time `t`, measured from the
    pixels (`RATIO`), and how many pixels it was measured on; `None` when the layer is missing."""
    if page.evaluate(OPACITY, [t, ident, nth]) is None:
        return None, 0
    shown = page.screenshot(clip=clip)
    page.evaluate(LAYER, [ident, nth, "hide"])
    page.evaluate(OPACITY, [t, ident, nth])
    hidden = page.screenshot(clip=clip)
    page.evaluate(LAYER, [ident, nth, "opaque"])
    page.evaluate(OPACITY, [t, ident, nth])
    opaque = page.screenshot(clip=clip)
    page.evaluate(LAYER, [ident, nth, "restore"])
    return page.evaluate(RATIO, [uri(shown), uri(hidden), uri(opaque)])


def opacity_errors(page, spec):
    """Every sample of the expectations' `opacities`, in the first loop and one cycle later: the
    largest difference between the opacity read (`OPACITY`) and the expected one, how many
    samples were read, how many were off by more than `OPACITY_TOL`, and the ids not found."""
    err, read, off, missing = 0.0, 0, 0, []
    for e in spec["opacities"]:
        for loop in (0, spec["cycle"]):
            for s in e["samples"]:
                o = page.evaluate(OPACITY, [s["t"] + loop, e["id"], e["nth"]])
                if o is None:
                    missing.append(e["id"])
                    continue
                read += 1
                err = max(err, abs(o - s["o"]))
                off += abs(o - s["o"]) > OPACITY_TOL
    return err, read, off, missing


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


# How long before the moment of comparison the switch probe shows the picture again, and the least
# time it keeps it hidden (seconds of the motion's clock).
SHOW_LEAD = 0.25
MIN_HIDDEN = 0.8


def rests_differ(a, b):
    """Whether two rests of the expectations certainly draw different pictures: an actor is in one
    and not the other, an actor's anchor is more than a pixel apart, or an actor is drawn
    otherwise (its fingerprint in `shapes` differs: a morph, whose anchor may stay)."""
    at_a = {x["id"]: x["at"] for x in a["actors"]}
    at_b = {x["id"]: x["at"] for x in b["actors"]}
    return at_a.keys() != at_b.keys() or any(math.dist(at_a[k], at_b[k]) > 1 for k in at_a) or \
        a.get("shapes", {}) != b.get("shapes", {})


# The version of the expectations' format this check reads (`PILeanTest.MotionChecks
# .expectationsFormat`).
FORMAT = 3


def spec_problem(spec):
    """Why the expectations cannot be checked, or `None`: another format than `FORMAT` (an older
    one has no opacities and no rests that are not stills, so that a fade would go unchecked), or
    other turns or slides than the motion declares (a writer that lost some)."""
    if spec.get("format", 1) != FORMAT or "declared" not in spec or "slides" not in spec or \
            "opacities" not in spec or \
            any(k not in r for r in spec["rests"] for k in ("shapes", "from", "still")):
        return (f"the expectations are in format {spec.get('format', 1)}, this check reads format "
                f"{FORMAT} (rests with their ends, drawings and whether they are stills, slides, "
                "opacities, declared moves): rebuild the expectations writer with this version "
                "of PILean")
    d = spec["declared"]
    if d["turns"] != len(spec["turns"]) or d["slides"] != len(spec["slides"]):
        return (f"the motion declares {d['turns']} turns and {d['slides']} slides, the "
                f"expectations list {len(spec['turns'])} and {len(spec['slides'])}")
    return None


def rest_window(rest):
    """The part of a rest where the probe may switch: the part in which the key is shown still
    (`from` to `until`, after the rest's fades) less 0.1 s at each end; `None` for a part of 0.3 s
    or less, which the probe does not use."""
    if rest["until"] - rest["from"] > 0.3:
        return rest["from"] + 0.1, rest["until"] - 0.1
    return None


def switch_times(spec, start=0.3):
    """The moments of the switch probe, from the expectations, for a clock at `start`: hidden
    inside one key's rest (`rest_window`) and compared inside a later key's rest that certainly
    draws another picture (`rests_differ`; shown again `SHOW_LEAD` before), at least
    `MIN_HIDDEN` later; the probe that is over soonest, as `(window, time to compare at)`, or
    `None` when no two rests certainly differ."""
    cycle = spec["cycle"]
    best = None
    rests = [r for r in spec["rests"] if rest_window(r)]
    for a in rests:
        lo_a, hi_a = rest_window(a)
        if (start - lo_a) % cycle <= hi_a - lo_a:
            wait, begin = 0.0, start
        else:
            wait, begin = (lo_a - start) % cycle, lo_a
        for b in rests:
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
    why = spec_problem(spec)
    if why:
        print(f"{name}: {why} -> FAILED")
        return False, 0
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
        for a in rest["actors"]:
            xy = first(seen["actors"], a["id"])
            if xy is None:
                ok = False
                print(f"{name}: key {rest['key']}: no element for {a['id']}")
                continue
            rest_err = max(rest_err, math.dist(xy, a["at"]))
        # the test writer writes the picture of every key, a key that is not a still included,
        # which the picture at the middle of its rest (`t`, after the rest's fades) must be
        still_file = os.path.abspath(os.path.join(root, f"{name}-key{rest['key']}.svg"))
        if not os.path.exists(still_file):
            ok = False
            print(f"{name}: key {rest['key']}: no file {os.path.basename(still_file)}")
            continue
        shot = page.screenshot(clip=clip)
        still_page = ctx.new_page()
        still_page.goto("file://" + still_file)
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
            still_page.goto("file://" + still_file)
            part_still = still_page.screenshot(clip=box_clip)
            still_page.close()
            n, f = unexplained(page, part, part_still)
            worst_ratio = max(worst_ratio, f)
            panel_pixels[panel["id"]] = max(panel_pixels.get(panel["id"], 0), n)
    # the second loop: every rest's anchors again, one cycle later
    for rest in spec["rests"]:
        seen = page.evaluate(READ, rest["t"] + spec["cycle"])
        uprights_found.add(len(seen["uprights"]))
        upright = max([upright] + [abs(a) for a, _ in seen["uprights"]])
        for a in rest["actors"]:
            xy = first(seen["actors"], a["id"])
            if xy is None:
                ok = False
                print(f"{name}: key {rest['key']}, second loop: no element for {a['id']}")
                continue
            rest_err = max(rest_err, math.dist(xy, a["at"]))
    loops = (0, spec["cycle"])
    for turn in spec["turns"]:
        c, s = turn["centre"], turn["start"]
        r = math.dist(s, c)
        a0 = math.degrees(math.atan2(s[1] - c[1], s[0] - c[0]))
        for off, sample in [(o, sm) for o in loops for sm in turn["samples"]]:
            seen = page.evaluate(READ, sample["t"] + off)
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
        for off, sample in [(o, sm) for o in loops for sm in sl["samples"]]:
            seen = page.evaluate(READ, sample["t"] + off)
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
    # opacities: every sample of every appearance and disappearance, in both loops, read from the
    # computed style, and in the first loop also measured from the pixels (`drawn_opacity`)
    listed = 2 * sum(len(e["samples"]) for e in spec["opacities"])
    opacity_err, opacity_read, opacity_off, opacity_missing = opacity_errors(page, spec)
    drawn_err, drawn_read = 0.0, 0
    for e in spec["opacities"]:
        for s in e["samples"]:
            o, pixels = drawn_opacity(page, clip, s["t"], e["id"], e["nth"])
            if o is not None:
                drawn_read += 1
                drawn_err = max(drawn_err, abs(o - s["o"]))
    if opacity_missing:
        ok = False
        print(f"{name}: no element for the fading {sorted(set(opacity_missing))}")
    opacities_ok = (opacity_read == listed and opacity_off == 0 and opacity_err <= OPACITY_TOL
                    and drawn_read == listed // 2 and drawn_err <= DRAWN_TOL)
    # panels in phase: every actor of every panel where the composed baker has it, at one time
    phase_err = {}
    for off, sample in [(o, sm) for o in loops for sm in spec.get("phase", [])]:
        seen = page.evaluate(READ, sample["t"] + off)
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
    if not times:
        print(f"{name}: the switch probe could not run: " +
              ("the motion has a single rest" if len(spec["rests"]) < 2 else
               "fewer than two rests show their key still for more than 0.3 s"
               if sum(1 for r in spec["rests"] if rest_window(r)) < 2 else
               "no two rests certainly draw different pictures (same actors, anchors and "
               "drawings)"))
    elif frozen == 0:
        print(f"{name}: the switch probe is undecided: the picture at {now:.2f} s (shown again) "
              f"draws the same as at {hidden_at or 0:.2f} s (hidden), although their rests "
              "differ, so a frozen picture would pass")
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
          and plays and panels_ok and opacities_ok)
    print(f"{name}: rests {rest_err:.2e} px and {rest_pixels} pixels off the stills (worst "
          f"blurred difference {worst_ratio:.3f} of the local contrast), "
          f"arcs {radius_err:.2e} px and {angle_err:.2e} deg over {len(spec['turns'])} turns, "
          f"slides {slide_err:.2e} px over {len(spec.get('slides', []))}, "
          f"opacities {opacity_err:.2e} over {opacity_read} of {listed} samples (drawn "
          f"{drawn_err:.3f} over {drawn_read}), "
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
    return ok, opacity_read


def opacity_mutation(browser, root, names):
    """The opacity check must catch a mark whose fade never starts and one whose fade runs at the
    wrong time: in the first motion whose expectations list opacities, the opacity animation of
    the group nearest the first entry's layer is held at 0 in the page, then (in a fresh page)
    has its values shifted one boundary later (`LAYER`, before seeking), and `opacity_errors` must
    find samples off each time. Returns whether it did both times."""
    for name in names:
        with open(os.path.join(root, name + ".json")) as f:
            spec = json.load(f)
        if not spec_problem(spec) and spec["opacities"]:
            break
    else:
        print("opacity mutation: no motion lists opacities -> FAILED")
        return False
    first_fade = spec["opacities"][0]
    caught_all = True
    for what, words in [("fade-never-starts", "never starts (its group's opacity animation held "
                         "at 0)"),
                        ("window-shifted", "runs one interval of the clock late (its values "
                         "shifted by one boundary, so the mark shows at the wrong time)")]:
        page = browser.new_page(viewport=VIEWPORT)
        page.goto("file://" + os.path.abspath(os.path.join(root, spec["svg"])))
        page.evaluate("document.documentElement.pauseAnimations()")
        held = page.evaluate(LAYER, [first_fade["id"], first_fade["nth"], what])
        _, read, off, _ = opacity_errors(page, spec)
        page.close()
        caught = held and off > 0
        caught_all = caught_all and caught
        print(f"opacity mutation ({what}): in {name} the fade of {first_fade['id']} {words}: "
              f"{off} of {read} samples off -> {'caught' if caught else 'NOT CAUGHT, FAILED'}")
    return caught_all


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
        engine = args[i + 1] if i + 1 < len(args) else ""
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
        verdicts = [check(browser, root, name) for name in names]
        failures += sum(0 if v else 1 for v, _ in verdicts)
        if not names:
            print(f"motion-browser-check: no motions in {root}")
            failures = 1
        else:
            failures += 0 if opacity_mutation(browser, root, names) else 1
        print(f"motion-browser-check ({engine}): {len(names)} motions, "
              f"{sum(n for _, n in verdicts)} opacity samples asserted, {failures} failures")
    finally:
        browser.close()
        pw.stop()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
