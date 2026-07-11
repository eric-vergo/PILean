# testdata/py — Pillow oracle scripts

Python side of PILean's correctness oracle. Pillow 11.3.0 is the ground
truth for "what should this file format decode to"; everything here is
deterministic (seeded) so the fixtures it writes are reproducible byte-for-
byte.

## Files

- **`praw.py`** — shared library (not a script): reader/writer for the
  `.praw` fixture format (see its module docstring for the exact byte
  layout, mirrored in `Tests/Praw.lean`) plus `image_to_praw_args` (Pillow
  image -> `.praw` args) and `resolve_rgba` (mode+data+palette -> a flat
  list of `(r,g,b,a)` pixels, mirroring `PILean.Image.getPixel!`'s
  promotion — this is what "pixel-exact" means throughout PILean's tests).
- **`pngsuite_truth.py`** — generates `testdata/corpus/pngsuite-truth/*.praw`
  from the vendored `testdata/corpus/pngsuite/*.png`. See its module
  docstring for PILean's exact 16-bit-to-8-bit normalization rules
  (truncate to the high byte, never round).
- **`gen_golden.py`** — the main entry point. Regenerates every fixture
  under `testdata/golden/` (the pattern matrix, the zlib corpus, the JPEG
  photo, the animated GIF) and, if `testdata/corpus/pngsuite/` is vendored,
  also refreshes `testdata/corpus/pngsuite-truth/`. Every random draw is
  seeded; see `testdata/golden/MANIFEST.md` (which this script also
  regenerates) for the exact seed table and rationale for every
  non-obvious choice (why RGBA has no `.bmp` fixture, why the JPEG photo
  is 64×64 not the usual 33×17, why `random200k` became `random100k`, …).
- **`crosscheck.py`** — verifies PILean's *own* codec output. Run after
  PILean's encoders have written files into `testdata/out/` (gitignored
  scratch space — nothing does yet, at WP8 time): for each output file
  named `<goldenname>.<ext>`, opens it with Pillow and compares against
  `testdata/golden/<goldenname>.praw` (or
  `testdata/corpus/pngsuite-truth/<goldenname>.praw`). Exact pixel match for
  png/bmp/ppm/pgm/gif/qoi, PSNR ≥ 30 dB for jpg. Handles a missing/empty
  `--dir` gracefully (prints a warning, exits 0).

## Usage

```sh
# Regenerate every golden fixture and the PngSuite truth corpus.
# Always review `git status`/`git diff --stat` afterward — goldens are
# checked in and never regenerated in CI.
python3 testdata/py/gen_golden.py

# After PILean's codecs write files into testdata/out/:
python3 testdata/py/crosscheck.py
python3 testdata/py/crosscheck.py --dir some/other/dir
```

## Design notes

- **Why an index+palette model for pattern generation?** Every pattern in
  `gen_golden.py` reduces to a small RGB palette plus a per-pixel index
  grid, and every mode variant (`l`/`la`/`rgb`/`rgba`/`p`) derives its
  pixel bytes from that *same* palette+grid — so `checker8_l_16x16` and
  `checker8_rgba_16x16` depict the identical image, just stored
  differently. This also makes P-mode generation exact (we choose the
  palette ourselves; no dependency on Pillow's — or any future PILean —
  quantizer).
- **Why compare resolved RGBA pixels instead of raw bytes in
  `crosscheck.py`?** GIF's palette is a well-known example of "same image,
  different valid encoding": Pillow's own GIF writer renumbers palette
  indices whenever the source palette has unused entries (verified
  empirically while building the `noise` pattern's P-mode fixtures, which
  intentionally leave some of a 256-entry palette unused). A PILean GIF
  encoder that reproduces the exact *colors* but picks different index
  numbers is correct; comparing raw index/palette bytes would wrongly
  fail it. `resolve_rgba` sidesteps this by comparing what the pixels
  actually mean, matching `Tests.Framework.assertImagesEq`'s semantics on
  the Lean side.
- **Dependencies**: standard library plus Pillow only (`pip install
  Pillow==11.3.0`). No other third-party packages (no numpy) — see
  `pngsuite_truth.py`'s docstring for how the 16-bit normalization avoids
  needing one.
