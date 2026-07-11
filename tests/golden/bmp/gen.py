#!/usr/bin/env python3
"""Generate PILean's BMP golden fixtures.

Run from anywhere with `python3 tests/golden/bmp/gen.py`. Requires Pillow
11.3.0. A few variants (top-down / negative-height, an 8-bit palette with
fewer than 256 entries) aren't produced by Pillow's own BMP writer, so
those are hand-crafted here byte-for-byte and then cross-checked by
having Pillow *read* them back (Pillow's BMP reader does support both).

The hand-crafted byte layout (BITMAPFILEHEADER + 40-byte BITMAPINFOHEADER,
BGR(A)/BGRX row order, bottom-up default, rows padded to 4 bytes) was
verified against Pillow 11.3.0's own writer output before being reused
here -- see WP4 notes.
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


def bmp_header(width: int, height: int, bpp: int, palette: bytes, data: bytes) -> bytes:
    """Build a minimal BITMAPFILEHEADER + BITMAPINFOHEADER(40) BI_RGB BMP.
    `height` may be negative for a top-down image."""
    ncolors = len(palette) // 4
    off = 14 + 40 + len(palette)
    filesize = off + len(data)
    fh = b"BM" + struct.pack("<IHHI", filesize, 0, 0, off)
    ih = struct.pack("<IiiHHIIiiII", 40, width, height, 1, bpp, 0, len(data),
                      2835, 2835, ncolors, 0)
    return fh + ih + palette + data


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
    # 1. 24-bit RGB, bottom-up, via Pillow's own writer. 4x3, distinct
    #    per-pixel colors so row/column order bugs show up immediately.
    w, h = 4, 3
    im = Image.new("RGB", (w, h))
    pixels = []
    for y in range(h):
        for x in range(w):
            c = (x * 20 + 5, y * 30 + 7, 100 + x + y)
            pixels.append(c)
            im.putpixel((x, y), c)
    im.save(os.path.join(HERE, "rgb24.bmp"))
    print(f"wrote rgb24.bmp ({os.path.getsize(os.path.join(HERE, 'rgb24.bmp'))} bytes)")
    check_pillow("rgb24.bmp", "RGB", pixels)

    # 2. 24-bit RGB, odd width (3): exercises row padding to a 4-byte
    #    boundary (rowBytes = 12 for 3 px * 3 B = 9 -> padded to 12).
    w, h = 3, 2
    im = Image.new("RGB", (w, h))
    pixels = []
    vals = [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12), (13, 14, 15), (16, 17, 18)]
    i = 0
    for y in range(h):
        for x in range(w):
            im.putpixel((x, y), vals[i]); pixels.append(vals[i]); i += 1
    im.save(os.path.join(HERE, "rgb24_pad.bmp"))
    print(f"wrote rgb24_pad.bmp ({os.path.getsize(os.path.join(HERE, 'rgb24_pad.bmp'))} bytes)")
    check_pillow("rgb24_pad.bmp", "RGB", pixels)

    # 3. 32-bit BGRA, bottom-up, via Pillow's own writer. Pillow's *reader*
    #    discards alpha (reports mode "RGB"), but its *writer* does encode
    #    real alpha bytes -- verified directly against the raw file bytes
    #    below rather than through Image.open.
    w, h = 2, 2
    im = Image.new("RGBA", (w, h))
    rgba_pixels = [(10, 20, 30, 40), (50, 60, 70, 80), (90, 100, 110, 120), (130, 140, 150, 160)]
    im.putpixel((0, 0), rgba_pixels[0])
    im.putpixel((1, 0), rgba_pixels[1])
    im.putpixel((0, 1), rgba_pixels[2])
    im.putpixel((1, 1), rgba_pixels[3])
    path = os.path.join(HERE, "rgba32.bmp")
    im.save(path)
    print(f"wrote rgba32.bmp ({os.path.getsize(path)} bytes)")
    data = open(path, "rb").read()
    off = struct.unpack_from("<I", data, 10)[0]
    body = data[off:]
    # bottom-up: file row 0 = image row 1 (bottom), row 1 = image row 0 (top)
    expected_body = bytearray()
    for (r, g, b, a) in [rgba_pixels[2], rgba_pixels[3]]:
        expected_body += bytes([b, g, r, a])
    for (r, g, b, a) in [rgba_pixels[0], rgba_pixels[1]]:
        expected_body += bytes([b, g, r, a])
    status = "OK" if bytes(body) == bytes(expected_body) else "MISMATCH"
    print(f"  raw BGRA bytes match hand-computed expectation: [{status}]")
    if bytes(body) != bytes(expected_body):
        raise SystemExit("rgba32.bmp byte layout mismatch")

    # 4. 8-bit paletted, via Pillow's own writer (256-entry palette).
    w, h = 4, 2
    im = Image.new("P", (w, h))
    pal = [0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 0]  # 5 colors
    im.putpalette(pal + [0] * (256 * 3 - len(pal)))
    idxs = [0, 1, 2, 3, 4, 0, 1, 2]
    k = 0
    for y in range(h):
        for x in range(w):
            im.putpixel((x, y), idxs[k]); k += 1
    im.save(os.path.join(HERE, "pal8.bmp"))
    print(f"wrote pal8.bmp ({os.path.getsize(os.path.join(HERE, 'pal8.bmp'))} bytes)")
    check_pillow("pal8.bmp", "P", idxs)

    # 5. 8-bit paletted, hand-crafted with clrUsed = 4 (< 256): exercises the
    #    "colorsUsed != 0" branch of the palette-size decode.
    palette_bgrx = bytes([0, 0, 0, 0,  0, 0, 255, 0,  0, 255, 0, 0,  255, 0, 0, 0])  # blk,red,grn,blu
    w, h = 2, 2
    idxs2 = [0, 1, 2, 3]  # top-left, top-right, bottom-left, bottom-right
    row_bytes = ((w + 3) // 4) * 4
    r_top = bytes([idxs2[0], idxs2[1]]) + bytes(row_bytes - 2)
    r_bot = bytes([idxs2[2], idxs2[3]]) + bytes(row_bytes - 2)
    body = r_bot + r_top  # bottom-up: bottom row first
    small = bmp_header(w, h, 8, palette_bgrx, body)
    write("pal8_small.bmp", small)
    check_pillow("pal8_small.bmp", "P", idxs2)
    if Image is not None:
        im5 = Image.open(os.path.join(HERE, "pal8_small.bmp"))
        pal5 = im5.getpalette()[:16]
        print("  Pillow-read palette (RGB * 4):", pal5)

    # 6. 24-bit RGB, hand-crafted TOP-DOWN (negative height), 2x2: exercises
    #    the top-down row-order branch, which Pillow's writer never emits.
    w, h = 2, 2
    td_pixels = [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12)]  # row-major, top-down
    row_bytes = ((w * 3 + 3) // 4) * 4
    rows = []
    for y in range(h):
        row = bytearray()
        for x in range(w):
            r, g, b = td_pixels[y * w + x]
            row += bytes([b, g, r])
        row += bytes(row_bytes - w * 3)
        rows.append(bytes(row))
    body = b"".join(rows)  # top-down: file row order == image row order
    topdown = bmp_header(w, -h, 24, b"", body)
    write("rgb24_topdown.bmp", topdown)
    check_pillow("rgb24_topdown.bmp", "RGB", td_pixels)

    # 7. Tiny 1x1 24-bit BMP.
    body1 = bytes([9, 8, 7]) + bytes(1)  # BGR + pad to 4
    tiny = bmp_header(1, 1, 24, b"", body1)
    write("tiny_1x1.bmp", tiny)
    check_pillow("tiny_1x1.bmp", "RGB", [(7, 8, 9)])

    print("\nAll BMP fixtures generated.")


if __name__ == "__main__":
    main()
