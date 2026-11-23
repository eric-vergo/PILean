# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# The same picture twice: renders each PDF that `lake exe pilean-test --pdf-out DIR` wrote with a
# PDF renderer already on the machine and compares it with PILean's PNG of the same picture
# (composited in sRGB, as PDF viewers composite). The renderers, each used when it is installed:
# Ghostscript (`gs`, at 96 dots per inch, so one pixel of the picture is one pixel, with
# anti-aliasing) and macOS's Quick Look (`qlmanage -t`, which draws with the system's PDF renderer,
# the one Preview uses, at the size of the picture). With `--qpdf`, every PDF is also checked by
# `qpdf --check`.
# Nothing is installed; the renderers write only into DIR.
#
# Usage, from the repository root:
#   lake exe pilean-test --pdf-out /tmp/pilean-pdf
#   python3 -I tools/pdf-compare.py /tmp/pilean-pdf [--qpdf]
# Exit status 1 when a figure is outside the tolerance (TOLERANCE below) for a renderer, or a
# PDF fails `qpdf --check`; 2 when no renderer is installed.

import glob
import importlib.util
import os
import shutil
import subprocess
import sys

# A figure passes when its mean absolute difference per sample is below MEAN levels and at least
# WITHIN of its pixels have every channel within LEVELS of PILean's PNG. Ghostscript renders the
# page at exactly one pixel per pixel of the picture, so its renders are judged; what is left
# between the two is the anti-aliasing of thin strokes and of the lettering (each renderer's
# own). Quick Look makes a thumbnail of the size asked for, resampled, so its pictures are
# reported, not judged: their edges move by a fraction of a pixel.
TOLERANCE = {"MEAN": 4.0, "WITHIN": 0.97, "LEVELS": 48}
JUDGED = {"gs"}


def load_compare_render():
    """The helpers of tools/compare-render.py (decode_rgb, compare, load_png_check), by path."""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "compare-render.py")
    spec = importlib.util.spec_from_file_location("compare_render", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def render_gs(pdf, out, size):
    """Renders the first page of pdf to the PNG out with Ghostscript at 96 dpi (size unused)."""
    subprocess.run(["gs", "-q", "-dSAFER", "-dBATCH", "-dNOPAUSE", "-sDEVICE=png16m", "-r96",
                    "-dGraphicsAlphaBits=4", "-dTextAlphaBits=4", "-o", out, pdf],
                   check=True, capture_output=True)


def render_quicklook(pdf, out, size):
    """Renders the first page of pdf to the PNG out with Quick Look, its larger side `size`
    pixels (the thumbnail lands in the folder of out as <pdf name>.png and is moved to out)."""
    folder = os.path.dirname(out)
    subprocess.run(["/usr/bin/qlmanage", "-t", "-s", str(size), "-o", folder, pdf],
                   check=True, capture_output=True)
    os.replace(os.path.join(folder, os.path.basename(pdf) + ".png"), out)


def main():
    """Renders and compares every <name>.pdf of the directory that has a <name>.png."""
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) != 1:
        sys.exit("usage: pdf-compare.py DIR [--qpdf]")
    d = args[0]
    use_qpdf = "--qpdf" in sys.argv
    cr = load_compare_render()
    cr.TOLERANCE = TOLERANCE
    png = cr.load_png_check()
    renderers = []
    if shutil.which("gs"):
        renderers.append(("gs", render_gs))
    if os.path.exists("/usr/bin/qlmanage"):
        renderers.append(("quicklook", render_quicklook))
    if not renderers:
        print("no PDF renderer is installed (gs, qlmanage): nothing compared")
        sys.exit(2)
    failures = 0
    summary = {}
    for pdf in sorted(glob.glob(os.path.join(d, "*.pdf"))):
        base = pdf[:-4]
        name = os.path.basename(base)
        if use_qpdf:
            r = subprocess.run(["qpdf", "--check", pdf], capture_output=True, text=True)
            if r.returncode != 0:
                print(f"{name}: qpdf --check FAILED: {r.stdout.strip()} {r.stderr.strip()}")
                failures += 1
        if not os.path.exists(base + ".png"):
            continue
        wa, ha, ours = cr.decode_rgb(png, base + ".png")
        for rname, render in renderers:
            out = f"{base}.{rname}.png"
            render(pdf, out, max(wa, ha))
            wb, hb, theirs = cr.decode_rgb(png, out)
            if (wa, ha) != (wb, hb):
                print(f"{name} [{rname}]: sizes differ ({wa}x{ha} and {wb}x{hb}): not compared")
                continue
            mean, within, worst = cr.compare(ours, theirs)
            ok = mean < TOLERANCE["MEAN"] and within >= TOLERANCE["WITHIN"]
            judged = rname in JUDGED
            failures += judged and not ok
            summary.setdefault(rname, []).append(mean)
            verdict = ("pass" if ok else "FAIL") if judged else "reported"
            print(f"{name} [{rname}]: mean difference {mean:.3f} levels, "
                  f"{100 * within:.2f} % of pixels within {TOLERANCE['LEVELS']} levels, "
                  f"largest {worst}: {verdict}")
    for rname, means in summary.items():
        mean = sum(means) / len(means)
        print(f"{rname}: {len(means)} pictures compared, mean difference {mean:.3f} levels "
              f"(largest {max(means):.3f})")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
