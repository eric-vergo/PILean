"""
Generate pixel-truth .praw fixtures for the vendored PngSuite corpus
(`tests/corpus/pngsuite/*.png`) into `tests/corpus/pngsuite-truth/*.praw`.

Corrupt files (named `x*.png` by PngSuite convention) get no truth; see
`tests/corpus/pngsuite/CORRUPT.txt`.

## PILean's "v1 normalization"

PILean does not (yet) support 16-bit pixel depth, so 16-bit source data is
downsampled to 8-bit by truncation (taking the high byte of each big-endian
16-bit sample) — never rounding. Concretely, per Pillow-decoded mode:

* `im.mode in ("RGB", "RGBA")` — Pillow's own PNG rawmode decoder already
  truncates 16-bit RGB(A) to 8-bit by dropping the low byte during raw
  unpacking (verified empirically: a `(0xABCD, 0x1256, 0x8000)` 16-bit pixel
  decodes to `(0xAB, 0x12, 0x80)`). Used as-is, no extra work.
* `im.mode == "I;16"` (16-bit grayscale, PNG color type 0 bit depth 16) —
  Pillow keeps full 16-bit precision natively (unlike RGB it does not
  auto-truncate), stored little-endian, 2 bytes/pixel via `im.tobytes()`.
  We take every second byte starting at offset 1 (`raw[1::2]`) — the high
  byte of each little-endian pair — to build 8-bit `L` data ourselves.
* `im.mode == "1"` (1-bit bilevel, PNG color type 0 bit depth 1) — Pillow
  already stores bilevel pixels as 0/255; `im.convert("L")` is a lossless
  relabeling.
* `im.mode == "L"` (PNG color type 0, bit depth 2/4/8) — Pillow's PNG
  decoder already scales 2-bit/4-bit samples to the full 8-bit range on
  load (bit replication), so `L` is used as-is.
* `im.mode == "P"` — stays `P`; the RGB palette (`im.getpalette()`) is
  folded with per-index alpha from `im.info['transparency']` into an RGBA
  palette (see `praw.image_to_praw_args`); tRNS is Pillow's only source of
  palette alpha since PNG has no separate palette-alpha chunk.
* `im.mode == "LA"` — as-is (PNG color type 4, bit depth 8 only; the 16-bit
  variant decodes straight to `RGBA`, handled by the RGB(A) case above).

No color management (gamma/ICC/sBIT) is applied — pixel *sample* values are
preserved exactly as encoded, only bit-depth is normalized.
"""
from __future__ import annotations

import sys
from pathlib import Path

from PIL import Image

import praw


def normalize(im: Image.Image) -> Image.Image:
    """Apply PILean's v1 normalization (see module docstring) to a
    freshly-opened PngSuite image, returning an image in one of PILean's
    five native modes (L, LA, RGB, RGBA, P)."""
    im.load()
    if im.mode == "1":
        return im.convert("L")
    if im.mode in ("I", "I;16", "I;16B", "I;16L", "I;16N"):
        im16 = im.convert("I;16")  # canonicalize to little-endian 16-bit raw
        raw = im16.tobytes()
        high = bytes(raw[1::2])
        return Image.frombytes("L", im16.size, high)
    if im.mode in praw.PIL_MODE_TO_CODE:
        return im
    raise ValueError(f"pngsuite_truth: unhandled Pillow mode {im.mode!r}")


def is_corrupt_name(name: str) -> bool:
    """PngSuite convention: files beginning with 'x' are intentionally
    corrupt/erroneous and carry no truth."""
    return name.startswith("x")


def generate(corpus_dir: Path, truth_dir: Path) -> tuple[int, int]:
    """Generate truth .praw files for every non-corrupt .png in
    `corpus_dir` into `truth_dir`. Returns `(generated, skipped)` counts."""
    truth_dir.mkdir(parents=True, exist_ok=True)
    pngs = sorted(corpus_dir.glob("*.png"))
    generated = 0
    skipped = 0
    corrupt_names = []
    for png in pngs:
        if is_corrupt_name(png.name):
            corrupt_names.append(png.name)
            skipped += 1
            continue
        im = Image.open(png)
        normed = normalize(im)
        mode, w, h, data, palette = praw.image_to_praw_args(normed)
        out = truth_dir / (png.stem + ".praw")
        praw.write_praw(out, mode, w, h, data, palette)
        generated += 1

    corrupt_list_path = corpus_dir / "CORRUPT.txt"
    lines = [
        "# Files with no pixel truth: PngSuite's 'x' naming convention marks",
        "# intentionally corrupt/erroneous test files (regardless of whether",
        "# a lenient decoder happens to open them). PILean's decoders must",
        "# reject these with an Except .error, never panic or hang.",
        "",
    ]
    for name in corrupt_names:
        lines.append(name)
    corrupt_list_path.write_text("\n".join(lines) + "\n")

    return generated, skipped


def main() -> None:
    root = Path(__file__).resolve().parent.parent  # tests/
    corpus_dir = root / "corpus" / "pngsuite"
    truth_dir = root / "corpus" / "pngsuite-truth"
    if not corpus_dir.exists() or not any(corpus_dir.glob("*.png")):
        print(f"pngsuite_truth: no vendored corpus at {corpus_dir}, skipping", file=sys.stderr)
        return
    generated, skipped = generate(corpus_dir, truth_dir)
    print(f"pngsuite_truth: wrote {generated} truth .praw files "
          f"({skipped} corrupt files skipped) into {truth_dir}")


if __name__ == "__main__":
    main()
