#!/usr/bin/env python3
"""
Pillow-oracle E2E check for PILean's GIF encoder (WP14-16).

Usage:
    python3 testdata/golden/gif-encode/gen.py

Steps:
1. Runs `lake exe tests --filter gif-encode-export`. That Lean test case
   (`Tests.GifTests`) builds three fixtures with `PILean.Gif.saveGif` and
   writes them to `testdata/out/gif-encode/`, alongside `.praw` ground
   truth for each (see `testdata/py/praw.py`) taken directly from the same
   in-memory `Image`s PILean's encoder was given:
     (a) single_palette16.gif   -- a single frame from a 16-color .palette
                                    image (the lossless "already-.palette"
                                    encode path).
     (b) animated_5frame.gif    -- 5 frames of a moving square on a flat
                                    background (<=16 distinct colors, so
                                    Image.quantize's exact-palette fast path
                                    applies -- still lossless), durationMs
                                    80, loopCount 0. animated_5frame_N.praw
                                    is frame N's ground truth.
     (c) gradient.gif           -- one RGB gradient frame with far more
                                    than 256 colors, forcing the lossy
                                    quantize path. gradient.praw is the
                                    *original*, pre-quantization pixels.
2. Opens every GIF with Pillow 11.3.0 and checks:
   (a) exact pixels vs. single_palette16.praw.
   (b) Pillow sees exactly 5 frames, each 80ms, loop == 0 (forever), and
       each frame's pixels (via `seek(n).convert("RGB")`) exactly match
       the corresponding animated_5frame_N.praw.
   (c) Pillow opens it, and the mean absolute pixel error (per channel)
       against gradient.praw's original pixels is < 12 -- a quantization
       *loss* bound, not exactness.
Exits nonzero on any failure.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from PIL import Image

ROOT = Path(__file__).resolve().parents[3]  # testdata/golden/gif-encode/gen.py -> repo root
sys.path.insert(0, str(ROOT / "testdata" / "py"))
import praw  # noqa: E402

OUT_DIR = ROOT / "testdata" / "out" / "gif-encode"


def run_export() -> None:
    """Run the Lean export test that (re)writes every fixture under OUT_DIR."""
    print("gen.py: running `lake exe tests --filter gif-encode-export` ...")
    result = subprocess.run(
        ["lake", "exe", "tests", "--filter", "gif-encode-export"],
        cwd=ROOT, capture_output=True, text=True,
    )
    print(result.stdout, end="")
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr)
        sys.exit(f"gen.py: gif-encode-export test failed (exit {result.returncode})")


def praw_rgba(path: Path) -> list[tuple[int, int, int, int]]:
    mode, w, h, data, pal = praw.read_praw(path)
    return praw.resolve_rgba(mode, w, h, data, pal)


def pil_rgba(im: Image.Image) -> list[tuple[int, int, int, int]]:
    mode, w, h, data, pal = praw.image_to_praw_args(im if im.mode in ("L", "LA", "RGB", "RGBA", "P")
                                                      else im.convert("RGB"))
    return praw.resolve_rgba(mode, w, h, data, pal)


def check_single_palette16() -> list[str]:
    failures = []
    path = OUT_DIR / "single_palette16.gif"
    truth_path = OUT_DIR / "single_palette16.praw"
    im = Image.open(path)
    im.load()
    got = pil_rgba(im)
    truth = praw_rgba(truth_path)
    if got != truth:
        n_bad = sum(a != b for a, b in zip(got, truth))
        failures.append(f"single_palette16.gif: {n_bad}/{len(truth)} pixels differ from truth")
    else:
        print(f"  ok    single_palette16.gif  (Pillow mode {im.mode}, exact match)")
    return failures


def check_animated_5frame() -> list[str]:
    failures = []
    path = OUT_DIR / "animated_5frame.gif"
    im = Image.open(path)
    if im.n_frames != 5:
        failures.append(f"animated_5frame.gif: expected 5 frames, Pillow sees {im.n_frames}")
        return failures
    if im.info.get("loop") != 0:
        failures.append(f"animated_5frame.gif: expected loop=0 (forever), got {im.info.get('loop')!r}")
    for i in range(5):
        im.seek(i)
        duration = im.info.get("duration")
        if duration != 80:
            failures.append(f"animated_5frame.gif frame {i}: expected duration=80ms, got {duration!r}")
        got = pil_rgba(im.convert("RGB"))
        truth = praw_rgba(OUT_DIR / f"animated_5frame_{i}.praw")
        if got != truth:
            n_bad = sum(a != b for a, b in zip(got, truth))
            failures.append(f"animated_5frame.gif frame {i}: {n_bad}/{len(truth)} pixels differ from truth")
        else:
            print(f"  ok    animated_5frame.gif frame {i}  (duration {duration}ms, exact match)")
    return failures


def check_gradient() -> list[str]:
    failures = []
    path = OUT_DIR / "gradient.gif"
    im = Image.open(path)
    im.load()
    got = pil_rgba(im.convert("RGB"))
    truth = praw_rgba(OUT_DIR / "gradient.praw")
    if len(got) != len(truth):
        failures.append(f"gradient.gif: pixel count mismatch ({len(got)} vs {len(truth)})")
        return failures
    total_abs_err = 0
    n_channels = 0
    for (gr, gg, gb, _ga), (tr, tg, tb, _ta) in zip(got, truth):
        total_abs_err += abs(gr - tr) + abs(gg - tg) + abs(gb - tb)
        n_channels += 3
    mae = total_abs_err / n_channels
    print(f"  gradient.gif mean absolute per-channel error vs. original: {mae:.3f}")
    if mae >= 12.0:
        failures.append(f"gradient.gif: mean absolute error {mae:.3f} >= 12.0 bound")
    else:
        print("  ok    gradient.gif  (within the quantization-loss bound)")
    return failures


def main() -> int:
    run_export()
    failures: list[str] = []
    failures += check_single_palette16()
    failures += check_animated_5frame()
    failures += check_gradient()
    print()
    if failures:
        print("Failures:")
        for f in failures:
            print(f"  FAIL {f}")
        return 1
    print("All GIF fixtures verified against Pillow.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
