#!/usr/bin/env python3
"""Generate PILean's QOI golden fixtures.

Run from anywhere with `python3 testdata/golden/qoi/gen.py`. Requires
Pillow 11.3.0, which has a native QOI encoder/decoder (verified empirically
for WP13 — `Image.registered_extensions()` includes `.qoi`). Every fixture
here is a real Pillow-encoded `.qoi` file, deliberately built to exercise
every op in the spec (`QOI_OP_RGB`/`RGBA`/`INDEX`/`DIFF`/`LUMA`/`RUN`) so
that PILean's decoder is checked against an independent encoder, not just
against itself. Ground truth for each is written alongside as a `.praw`
fixture (see `testdata/py/praw.py`) — `Tests/QoiTests.lean` loads both and
compares PILean's decode against the `.praw` pixels.
"""
import os
import sys
from pathlib import Path

from PIL import Image

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "py"))
import praw  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def write_pair(name: str, im: Image.Image) -> None:
    """Write `<name>.qoi` (Pillow's own encoder) and `<name>.praw` (ground
    truth pixels, from the same in-memory image Pillow just encoded)."""
    qoi_path = os.path.join(HERE, f"{name}.qoi")
    im.save(qoi_path, format="QOI")
    print(f"wrote {name}.qoi ({os.path.getsize(qoi_path)} bytes)")

    # Round-trip through Pillow's own reader for the .praw truth, rather than
    # trusting `im` directly -- this is what Pillow itself decodes the file
    # back to, which is the actual oracle for PILean's decoder.
    decoded = Image.open(qoi_path)
    decoded.load()
    mode, w, h, data, pal = praw.image_to_praw_args(decoded)
    praw_path = os.path.join(HERE, f"{name}.praw")
    praw.write_praw(praw_path, mode, w, h, data, pal)
    print(f"wrote {name}.praw")


def main() -> None:
    # 1. RGB, 6x5: mostly-repeating runs (exercises QOI_OP_RUN, including a
    #    run that hits the 62-pixel cap is out of scope at this size but the
    #    ordinary 1..N run path is), tiny per-pixel deltas (QOI_OP_DIFF),
    #    larger-but-still-close deltas (QOI_OP_LUMA), a repeated earlier
    #    color (QOI_OP_INDEX), and one big jump (QOI_OP_RGB).
    w, h = 6, 5
    base = (40, 80, 120)
    pixels = []
    prev = base
    for i in range(w * h):
        if i in (0, 1, 2, 3):
            c = base  # a run of 4 identical pixels
        elif i == 4:
            c = (base[0] + 1, base[1] - 1, base[2] + 1)  # QOI_OP_DIFF
        elif i == 5:
            c = (base[0] + 1, base[1] - 1, base[2] + 1)  # repeats -> QOI_OP_INDEX
        elif i == 6:
            c = (base[0] + 6, base[1] - 7, base[2] + 5)  # QOI_OP_LUMA
        elif i == 7:
            c = (10, 200, 30)  # big jump -> QOI_OP_RGB
        elif i == 8:
            c = base  # QOI_OP_INDEX (the very first color, slot still valid)
        else:
            # a smooth-ish walk so later rows exercise a mix of DIFF/LUMA/RGB
            step = (i * 37) % 5 - 2
            c = (max(0, min(255, prev[0] + step)),
                 max(0, min(255, prev[1] + step * 2)),
                 max(0, min(255, prev[2] - step)))
        pixels.append(c)
        prev = c
    im = Image.new("RGB", (w, h))
    im.putdata(pixels)
    write_pair("ref_rgb", im)

    # 2. RGBA, 4x4: alpha changes force QOI_OP_RGBA (DIFF/LUMA never touch
    #    alpha), plus repeats and an index hit.
    w, h = 4, 4
    pixels_rgba = [
        (10, 20, 30, 255), (10, 20, 30, 255), (10, 20, 30, 255), (10, 20, 30, 128),
        (11, 19, 31, 128), (200, 5, 5, 255), (200, 5, 5, 255), (10, 20, 30, 255),
        (0, 0, 0, 0), (255, 255, 255, 255), (255, 255, 255, 255), (1, 2, 3, 4),
        (250, 251, 252, 253), (250, 251, 252, 253), (10, 20, 30, 255), (10, 20, 30, 255),
    ]
    im2 = Image.new("RGBA", (w, h))
    im2.putdata(pixels_rgba)
    write_pair("ref_rgba", im2)

    # 3. Tiny 1x1 RGB.
    im3 = Image.new("RGB", (1, 1))
    im3.putdata([(7, 8, 9)])
    write_pair("ref_1x1", im3)

    print("\nAll QOI fixtures generated.")


if __name__ == "__main__":
    main()
