# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# The same picture twice: compares PILean's PNG of each gallery figure with the figure's SVG as
# macOS renders it. `lake exe pilean-test --compare-out DIR` writes DIR/<name>-notext.svg and two
# PNGs without text (text is left out of this comparison): <name>-notext.png, mixed in linear light
# as PILean draws, and <name>-notext-srgb.png, mixed in the sRGB encoding as macOS (like most
# renderers) mixes. This script renders each SVG with `sips` (no window; its output goes into DIR),
# decodes the PNGs with the standard library, and compares their RGB samples. The sRGB-mixed PNG
# must match within the tolerance: that checks the geometry, coverage and colours. The linear one
# is reported too; it differs where edges are anti-aliased and where colours overlap, by design.
# Uses only the Python standard library and the system's `sips`; installs nothing.
#
# Usage, from the repository root:
#   lake exe pilean-test --compare-out /tmp/pilean-compare
#   /usr/bin/python3 -I tools/compare-render.py /tmp/pilean-compare
# Exit status 1 when a figure is outside the tolerance (see TOLERANCE below).

import glob
import importlib.util
import os
import subprocess
import sys
import zlib

# A figure passes when its mean absolute difference per sample is below MEAN and at least
# WITHIN of its pixels have every channel within LEVELS of the other renderer's.
TOLERANCE = {"MEAN": 1.0, "WITHIN": 0.99, "LEVELS": 32}


def load_png_check():
    """The PNG helpers of tools/png-check.py (parse_png, unfilter), loaded by path."""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "png-check.py")
    spec = importlib.util.spec_from_file_location("png_check", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def decode_rgb(png, path):
    """The RGB samples of an 8-bit, non-interlaced grey, RGB or RGBA PNG, as (w, h, bytes);
    alpha is composited over white, as both renderers' backgrounds are white."""
    chunks, (w, h, depth, ctype, interlace) = png.parse_png(open(path, "rb").read())
    if depth != 8 or interlace != 0 or ctype not in (0, 2, 6):
        raise ValueError(f"{path}: unsupported PNG (depth {depth}, type {ctype})")
    ch = {0: 1, 2: 3, 6: 4}[ctype]
    data = zlib.decompress(b"".join(d for t, d in chunks if t == b"IDAT"))
    raw = png.unfilter(data, w, h, ch, w * ch)
    out = bytearray()
    for i in range(w * h):
        px = raw[i * ch:(i + 1) * ch]
        if ch == 1:
            out += bytes((px[0],) * 3)
        elif ch == 3:
            out += px
        else:
            a = px[3]
            out += bytes((px[k] * a + 255 * (255 - a) + 127) // 255 for k in range(3))
    return w, h, bytes(out)


def compare(a, b):
    """The mean absolute sample difference, the share of pixels within LEVELS, and the
    largest difference of two RGB sample strings of equal size."""
    n = len(a) // 3
    total, within, worst = 0, 0, 0
    for i in range(n):
        d = max(abs(a[3 * i + k] - b[3 * i + k]) for k in range(3))
        total += sum(abs(a[3 * i + k] - b[3 * i + k]) for k in range(3))
        worst = max(worst, d)
        within += d <= TOLERANCE["LEVELS"]
    return total / (3 * n), within / n, worst


def main():
    """Renders and compares every *-notext.svg of the directory given."""
    if len(sys.argv) != 2:
        sys.exit("usage: compare-render.py DIR")
    d = sys.argv[1]
    png = load_png_check()
    failures = 0
    for svg in sorted(glob.glob(os.path.join(d, "*-notext.svg"))):
        base = svg[:-4]
        ref = base + ".sips.png"
        subprocess.run(["/usr/bin/sips", "-s", "format", "png", svg, "--out", ref],
                       check=True, capture_output=True)
        wb, hb, theirs = decode_rgb(png, ref)
        for suffix, judged in (("-srgb", True), ("", False)):
            wa, ha, ours = decode_rgb(png, base + suffix + ".png")
            name = os.path.basename(base) + suffix
            if (wa, ha) != (wb, hb):
                print(f"{name}: sizes differ ({wa}x{ha} and {wb}x{hb})")
                failures += judged
                continue
            mean, within, worst = compare(ours, theirs)
            ok = mean < TOLERANCE["MEAN"] and within >= TOLERANCE["WITHIN"]
            failures += judged and not ok
            verdict = ("pass" if ok else "FAIL") if judged else "reported"
            print(f"{name}: mean difference {mean:.3f} levels, "
                  f"{100 * within:.2f} % of pixels within {TOLERANCE['LEVELS']} levels, "
                  f"largest {worst}: {verdict}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
