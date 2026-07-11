#!/usr/bin/env python3
"""
Cross-check PILean's own encoder output against the Pillow oracle.

CLI:
    python3 testdata/py/crosscheck.py [--dir testdata/out]

For every image file under `--dir` whose stem matches a fixture name (i.e.
named `<goldenname>.<ext>` where `testdata/golden/<goldenname>.praw` — or
`testdata/corpus/pngsuite-truth/<goldenname>.praw` — exists), this opens it
with Pillow and compares its decoded pixels against that `.praw` ground
truth:

- **png / bmp / ppm / pgm / gif**: pixels must match exactly, compared
  after promoting every pixel to RGBA the same way `PILean.Image.getPixel!`
  does (gray -> `(v,v,v,255)`, grayAlpha -> `(v,v,v,a)`, rgb ->
  `(r,g,b,255)`, rgba as-is, palette -> palette lookup) — deliberately
  *not* raw storage bytes, since e.g. GIF encoders are free to renumber
  palette indices without changing the decoded image (Pillow's own GIF
  writer does exactly this whenever the source palette has unused
  entries).
- **jpg / jpeg**: lossy; requires PSNR ≥ 30 dB against the truth instead
  of exact equality.
- **qoi**: skipped (with a note) if this Pillow build has no QOI plugin;
  otherwise treated like png/bmp/etc.
- any other extension PILean might write that Pillow can still open: we
  just verify Pillow *can* open it (produces no truth-comparison, since we
  have no independent oracle for it) — this still catches "wrote garbage
  no reader can parse".

Files with no matching `.praw` (e.g. `checker_anim.gif`, which is
multi-frame and has no single-frame truth) are skipped with a warning, not
a failure — not every golden fixture is meant to be pixel-compared this
way.

Exits nonzero (and prints a per-file report) if anything fails. Handles a
missing/empty `--dir` gracefully (nothing has been written to `testdata/out/`
by any codec yet at WP8 time — that's fine, not a failure).
"""
from __future__ import annotations

import argparse
import math
import re
import sys
from pathlib import Path

from PIL import Image, UnidentifiedImageError

import praw

ROOT = Path(__file__).resolve().parent.parent  # testdata/
GOLDEN = ROOT / "golden"
PNGSUITE_TRUTH = ROOT / "corpus" / "pngsuite-truth"

EXACT_EXTS = {".png", ".bmp", ".ppm", ".pgm", ".gif", ".qoi"}
JPEG_EXTS = {".jpg", ".jpeg"}
PSNR_THRESHOLD_DB = 30.0

# Pillow builds without a QOI plugin raise UnidentifiedImageError for .qoi
# (Pillow 11.3.0 itself does support QOI natively); detect that once up
# front so we can downgrade those specific failures to a skip-with-note
# instead of a hard failure on older/different Pillow builds.
_HAS_QOI = ".qoi" in Image.registered_extensions()


_QUALITY_SUFFIX = re.compile(r"_q\d+$")


def find_truth(stem: str) -> Path | None:
    """Look up `<stem>.praw` in `testdata/golden/` then
    `testdata/corpus/pngsuite-truth/`. JPEG fixtures are named
    `<base>_q<N>.jpg` for several quality levels sharing one
    `<base>.praw` truth (the pre-compression source pixels — JPEG is
    compared by PSNR, not exact match, so every quality level legitimately
    shares the same ground truth); if the exact stem has no truth, retry
    with a trailing `_q<N>` suffix stripped."""
    stems = [stem]
    stripped = _QUALITY_SUFFIX.sub("", stem)
    if stripped != stem:
        stems.append(stripped)
    for s in stems:
        for candidate in (GOLDEN / f"{s}.praw", PNGSUITE_TRUTH / f"{s}.praw"):
            if candidate.exists():
                return candidate
    return None


def psnr(a: list[tuple[int, int, int, int]], b: list[tuple[int, int, int, int]]) -> float:
    n = len(a)
    if n == 0:
        return math.inf
    se = 0
    for (ar, ag, ab, _aa), (br, bg, bb, _ba) in zip(a, b):
        se += (ar - br) ** 2 + (ag - bg) ** 2 + (ab - bb) ** 2
    mse = se / (n * 3)
    if mse == 0:
        return math.inf
    return 10 * math.log10((255 * 255) / mse)


class Report:
    def __init__(self) -> None:
        self.checked = 0
        self.skipped = 0
        self.failures: list[str] = []

    def fail(self, path: Path, msg: str) -> None:
        self.failures.append(f"{path}: {msg}")

    def skip(self, path: Path, msg: str) -> None:
        self.skipped += 1
        print(f"  SKIP  {path.name}: {msg}")


def check_file(path: Path, report: Report) -> None:
    stem = path.stem
    ext = path.suffix.lower()

    truth_path = find_truth(stem)
    if truth_path is None:
        report.skip(path, "no matching <stem>.praw truth found (not every fixture needs one)")
        return

    try:
        im = Image.open(path)
        im.load()
    except UnidentifiedImageError as e:
        if ext == ".qoi" and not _HAS_QOI:
            report.skip(path, "Pillow build has no QOI plugin; cannot verify pixels "
                        "(file was at least written; not independently checkable here)")
            return
        report.fail(path, f"Pillow could not open a file PILean wrote: {e}")
        return
    except Exception as e:  # noqa: BLE001 - report, don't crash the whole run
        report.fail(path, f"Pillow raised opening this file: {type(e).__name__}: {e}")
        return

    mode_t, w_t, h_t, data_t, pal_t = praw.read_praw(truth_path)
    try:
        mode_g, w_g, h_g, data_g, pal_g = praw.image_to_praw_args(im)
    except ValueError as e:
        report.fail(path, f"unsupported Pillow mode after opening: {e}")
        return

    if (w_g, h_g) != (w_t, h_t):
        report.fail(path, f"size mismatch: got {w_g}x{h_g}, truth is {w_t}x{h_t}")
        return

    truth_px = praw.resolve_rgba(mode_t, w_t, h_t, data_t, pal_t)
    got_px = praw.resolve_rgba(mode_g, w_g, h_g, data_g, pal_g)

    if ext in JPEG_EXTS:
        p = psnr(truth_px, got_px)
        report.checked += 1
        if p < PSNR_THRESHOLD_DB:
            report.fail(path, f"PSNR {p:.2f} dB < {PSNR_THRESHOLD_DB} dB threshold "
                        f"(truth {truth_path.relative_to(ROOT)})")
        else:
            print(f"  ok    {path.name}  (PSNR {p:.2f} dB)")
        return

    if ext in EXACT_EXTS:
        report.checked += 1
        if truth_px != got_px:
            first = next((i for i in range(len(truth_px)) if truth_px[i] != got_px[i]), None)
            detail = ""
            if first is not None:
                x, y = first % w_t, first // w_t
                detail = f"; first mismatch at ({x},{y}): got {got_px[first]}, " \
                          f"expected {truth_px[first]}"
            report.fail(path, f"{sum(a != b for a, b in zip(truth_px, got_px))} of "
                        f"{len(truth_px)} pixels differ from truth "
                        f"(truth {truth_path.relative_to(ROOT)}){detail}")
        else:
            print(f"  ok    {path.name}")
        return

    # Unknown extension PILean might write: opening successfully already
    # proved something. Still compare pixels since we have a truth file.
    report.checked += 1
    if truth_px != got_px:
        report.fail(path, f"pixels differ from truth {truth_path.relative_to(ROOT)} "
                    f"(extension {ext!r} has no dedicated comparison rule; used exact)")
    else:
        print(f"  ok    {path.name}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dir", default=str(ROOT / "out"),
                     help="directory of PILean-written files to verify (default: testdata/out)")
    args = ap.parse_args()
    out_dir = Path(args.dir)

    if not out_dir.exists():
        print(f"crosscheck: {out_dir} does not exist yet (nothing written by PILean) — "
              "nothing to check, treating as success.")
        return 0

    files = sorted(p for p in out_dir.rglob("*") if p.is_file())
    if not files:
        print(f"crosscheck: {out_dir} is empty — nothing to check, treating as success.")
        return 0

    report = Report()
    print(f"crosscheck: checking {len(files)} file(s) under {out_dir}")
    for f in files:
        check_file(f, report)

    print(f"\n{report.checked} checked, {report.skipped} skipped, "
          f"{len(report.failures)} failed")
    if report.failures:
        print("\nFailures:")
        for f in report.failures:
            print(f"  FAIL {f}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
