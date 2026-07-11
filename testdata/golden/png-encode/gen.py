#!/usr/bin/env python3
"""
Pillow-oracle E2E check for PILean's PNG encoder (WP11).

Usage:
    python3 testdata/golden/png-encode/gen.py

Steps:
1. Runs `lake exe tests --filter png-encode-export`. That Lean test case
   loads a fixed set of images from committed `testdata/golden/*.praw`
   fixtures (modes gray/rgb/rgba/palette; sizes 16x16, 33x17, 1x1; checker,
   noise, and flat pixel patterns), encodes each with PILean's own PNG
   encoder (`PILean.Png.encode`), and writes the result to
   `testdata/out/png-encode/<name>.png`.
2. Opens every `.png` written there with Pillow 11.3.0 and pixel-compares
   it against the *same* `.praw` fixture PILean's encoder was given as
   input — the same ground truth, decoded independently. This is therefore
   a genuine round trip through an external decoder even though PILean has
   no PNG decoder of its own yet (WP12): "did Pillow read back byte-for-
   byte what PILean's encoder was asked to draw?".

This is deliberately not a golden-fixture generator in the usual sense —
there is no golden PNG byte stream to freeze here, since the encoder's
output bytes will change once WP10's real DEFLATE (fixed/dynamic Huffman)
lands; only pixel content is checked. Run manually, report the output in
the work package notes. Exits nonzero on any failure.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from PIL import Image

ROOT = Path(__file__).resolve().parents[3]  # testdata/golden/png-encode/gen.py -> repo root
sys.path.insert(0, str(ROOT / "testdata" / "py"))
import praw  # noqa: E402

GOLDEN = ROOT / "testdata" / "golden"
OUT_DIR = ROOT / "testdata" / "out" / "png-encode"


def run_export() -> None:
    """Run the Lean export test that (re)writes every PNG under OUT_DIR."""
    print("gen.py: running `lake exe tests --filter png-encode-export` ...")
    result = subprocess.run(
        ["lake", "exe", "tests", "--filter", "png-encode-export"],
        cwd=ROOT, capture_output=True, text=True,
    )
    print(result.stdout, end="")
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr)
        sys.exit(f"gen.py: png-encode-export test failed (exit {result.returncode})")


def check_all() -> int:
    """Pillow-open and pixel-compare every PNG under OUT_DIR against its
    same-named .praw truth in GOLDEN. Returns a process exit code."""
    if not OUT_DIR.exists():
        sys.exit(f"gen.py: {OUT_DIR} does not exist — did the export test run?")
    pngs = sorted(OUT_DIR.glob("*.png"))
    if not pngs:
        sys.exit(f"gen.py: no .png files found under {OUT_DIR}")

    failures: list[str] = []
    for png in pngs:
        truth_path = GOLDEN / f"{png.stem}.praw"
        if not truth_path.exists():
            failures.append(f"{png.name}: no matching truth {truth_path}")
            continue
        try:
            im = Image.open(png)
            im.load()
        except Exception as e:  # noqa: BLE001 - report, don't crash the whole run
            failures.append(f"{png.name}: Pillow could not open: {type(e).__name__}: {e}")
            continue

        mode_t, w_t, h_t, data_t, pal_t = praw.read_praw(truth_path)
        try:
            mode_g, w_g, h_g, data_g, pal_g = praw.image_to_praw_args(im)
        except ValueError as e:
            failures.append(f"{png.name}: unsupported Pillow mode after opening: {e}")
            continue

        if (w_g, h_g) != (w_t, h_t):
            failures.append(f"{png.name}: size mismatch: got {w_g}x{h_g}, truth {w_t}x{h_t}")
            continue

        truth_px = praw.resolve_rgba(mode_t, w_t, h_t, data_t, pal_t)
        got_px = praw.resolve_rgba(mode_g, w_g, h_g, data_g, pal_g)
        if truth_px != got_px:
            n_bad = sum(a != b for a, b in zip(truth_px, got_px))
            first = next((i for i in range(len(truth_px)) if truth_px[i] != got_px[i]), None)
            detail = ""
            if first is not None:
                x, y = first % w_t, first // w_t
                detail = f"; first mismatch at ({x},{y}): got {got_px[first]}, expected {truth_px[first]}"
            failures.append(
                f"{png.name}: {n_bad}/{len(truth_px)} pixels differ from "
                f"{truth_path.relative_to(ROOT)}{detail}"
            )
            continue

        print(f"  ok    {png.name}  (Pillow mode {im.mode}, matches {truth_path.name})")

    print(f"\n{len(pngs) - len(failures)}/{len(pngs)} PNGs verified against Pillow + .praw truth")
    if failures:
        print("\nFailures:")
        for f in failures:
            print(f"  FAIL {f}")
        return 1
    return 0


def main() -> int:
    run_export()
    return check_all()


if __name__ == "__main__":
    sys.exit(main())
