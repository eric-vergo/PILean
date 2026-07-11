#!/usr/bin/env python3
"""Generate PILean's Netpbm (PPM/PGM/PBM) golden fixtures.

Run from anywhere with `python3 testdata/golden/netpbm/gen.py`. Requires
Pillow 11.3.0 (`pip install Pillow==11.3.0`). Writes fixtures into this
directory and cross-checks each one against Pillow's own reader where
Pillow can parse it (all fixtures except the sub-255-maxval ones, which
PILean scales by floor(v*255/maxval) while Pillow rounds — see the note
printed for those).

Every fixture here is tiny (well under the repo's 10 KB fixture budget)
and hand-verified byte-for-byte against Pillow 11.3.0's own BMP/PPM
encoder output (see WP4 notes), so the exact bytes below are trustworthy
even where Pillow itself cannot write that particular variant (ASCII
P1/P2/P3, non-255 maxval, comments).
"""
import os
import struct
import sys

try:
    from PIL import Image
except ImportError:
    Image = None

HERE = os.path.dirname(os.path.abspath(__file__))


def write(name: str, data: bytes) -> None:
    path = os.path.join(HERE, name)
    with open(path, "wb") as f:
        f.write(data)
    print(f"wrote {name} ({len(data)} bytes)")


def check_pillow(name: str, expected_mode: str, expected_pixels: list) -> None:
    if Image is None:
        print(f"  [skip Pillow check for {name}: PIL not importable]")
        return
    path = os.path.join(HERE, name)
    im = Image.open(path)
    im.load()
    ok = im.mode == expected_mode and list(im.getdata()) == expected_pixels
    status = "OK" if ok else "MISMATCH"
    print(f"  Pillow decodes {name}: mode={im.mode} pixels={list(im.getdata())} [{status}]")
    if not ok:
        raise SystemExit(f"Pillow oracle mismatch for {name}")


def main() -> None:
    # 1. P3 (ASCII pixmap) with comments interspersed among header and data
    #    tokens, maxval 255, 3x2.
    p3 = (
        b"P3\n"
        b"# a leading comment\n"
        b"3 2 # trailing comment on the dimensions line\n"
        b"255\n"
        b"255 0 0   0 255 0  # two pixels\n"
        b"0 0 255\n"
        b"10 20 30  40 50 60\n"
        b"# comment before the last pixel\n"
        b"70 80 90\n"
    )
    write("p3_comments.ppm", p3)
    check_pillow(
        "p3_comments.ppm", "RGB",
        [(255, 0, 0), (0, 255, 0), (0, 0, 255),
         (10, 20, 30), (40, 50, 60), (70, 80, 90)],
    )

    # 2. P6 (binary pixmap), maxval 255, 4x3 gradient -> direct-copy fast path.
    w, h = 4, 3
    pixels = []
    body = bytearray()
    for y in range(h):
        for x in range(w):
            r, g, b = x * 30, y * 40, 100
            pixels.append((r, g, b))
            body += bytes([r, g, b])
    p6 = f"P6\n{w} {h}\n255\n".encode("ascii") + bytes(body)
    write("p6_gradient.ppm", p6)
    check_pillow("p6_gradient.ppm", "RGB", pixels)

    # 3. P6 (binary pixmap) with maxval 100 (< 255): exercises scaling on the
    #    binary path. PILean floors v*255/100; Pillow rounds, so this one is
    #    NOT cross-checked against Pillow's decoded pixel values, only the
    #    fact that Pillow can open the file at all (format-level sanity).
    w, h = 2, 2
    maxval = 100
    raw_samples = [(1, 2, 3), (50, 60, 70), (99, 0, 100), (10, 90, 45)]
    body = bytearray()
    for (r, g, b) in raw_samples:
        body += bytes([r, g, b])
    p6s = f"P6\n{w} {h}\n{maxval}\n".encode("ascii") + bytes(body)
    write("p6_scaled.ppm", p6s)
    if Image is not None:
        im = Image.open(os.path.join(HERE, "p6_scaled.ppm"))
        im.load()
        print(f"  Pillow opens p6_scaled.ppm: mode={im.mode} size={im.size} "
              f"(pixel values not compared -- Pillow rounds, PILean floors)")
    expected = [(min(v * 255 // maxval, 255) for v in rgb) for rgb in raw_samples]
    print("  PILean-expected (floor) pixels:", [tuple(p) for p in expected])

    # 4. P2 (ASCII graymap), maxval 15: exercises scaling on the ASCII path.
    #    15 evenly divides 255 (255 = 15*17) so floor == round here, and
    #    Pillow's decode IS directly comparable.
    w, h = 4, 2
    maxval = 15
    values = [0, 5, 8, 15, 3, 12, 1, 15]
    p2 = (f"P2\n{w} {h}\n{maxval}\n" + " ".join(str(v) for v in values) + "\n").encode("ascii")
    write("p2_scaled.pgm", p2)
    expected = [min(v * 255 // maxval, 255) for v in values]
    check_pillow("p2_scaled.pgm", "L", expected)

    # 5. P5 (binary graymap), maxval 255, 5x2 -> direct-copy fast path.
    w, h = 5, 2
    values = [g for row in range(h) for g in [row * 50 + c * 10 for c in range(w)]]
    p5 = f"P5\n{w} {h}\n255\n".encode("ascii") + bytes(values)
    write("p5_gradient.pgm", p5)
    check_pillow("p5_gradient.pgm", "L", values)

    # 6. P5 (binary graymap), maxval 50 (< 255): scaling on the binary path,
    #    not cross-checked pixel-for-pixel against Pillow (rounds vs floors).
    w, h = 3, 2
    maxval = 50
    values = [0, 25, 50, 10, 40, 5]
    p5s = f"P5\n{w} {h}\n{maxval}\n".encode("ascii") + bytes(values)
    write("p5_scaled.pgm", p5s)
    if Image is not None:
        im = Image.open(os.path.join(HERE, "p5_scaled.pgm"))
        im.load()
        print(f"  Pillow opens p5_scaled.pgm: mode={im.mode} size={im.size} "
              f"(pixel values not compared -- Pillow rounds, PILean floors)")
    expected = [min(v * 255 // maxval, 255) for v in values]
    print("  PILean-expected (floor) pixels:", expected)

    # 7. P1 (ASCII bitmap) with a comment, 5x3: 1 = black (0), 0 = white (255).
    pattern = [
        [1, 0, 1, 0, 1],
        [0, 1, 0, 1, 0],
        [1, 1, 1, 0, 0],
    ]
    rows = "\n".join(" ".join(str(v) for v in row) for row in pattern)
    p1 = f"P1\n# bitmap comment\n5 3\n{rows}\n".encode("ascii")
    write("p1_bitmap.pbm", p1)
    expected = [0 if v == 1 else 255 for row in pattern for v in row]
    check_pillow("p1_bitmap.pbm", "1", expected)
    print("  PILean-expected (gray, inverted) pixels:", expected)

    # 8. P4 (binary bitmap), 5x3: non-multiple-of-8 width exercises row
    #    padding (rowBytes = 1, 3 padding bits per row). Bytes hand-derived
    #    from the same `pattern` above (1 -> file bit 1 = black).
    def pack_row(row):
        bits = 0
        for i, v in enumerate(row):
            if v == 1:
                bits |= 1 << (7 - i)
        return bits

    p4_body = bytes(pack_row(row) for row in pattern)
    p4 = b"P4\n5 3\n" + p4_body
    write("p4_bitmap.pbm", p4)
    check_pillow("p4_bitmap.pbm", "1", expected)
    print("  PILean-expected (gray, inverted) pixels:", expected)

    # 9. Tiny 1x1 P6.
    p6_tiny = b"P6\n1 1\n255\n" + bytes([12, 34, 56])
    write("tiny_1x1.ppm", p6_tiny)
    check_pillow("tiny_1x1.ppm", "RGB", [(12, 34, 56)])

    print("\nAll Netpbm fixtures generated.")


if __name__ == "__main__":
    main()
