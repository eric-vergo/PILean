"""
Shared .praw (PILean raw fixture) reader/writer.

.praw is PILean's format-agnostic pixel-truth interchange format: a tiny
container that stores an image's decoded pixels exactly as PILean's
`PILean.Image` would hold them in memory, so any codec's decoder output can
be compared byte-for-byte against a fixed oracle value without depending on
any *other* codec (in particular, without depending on PILean's own PNG
encoder being correct).

Byte layout (all multi-byte integers little-endian):

    offset  size  field
    0       4     magic, ASCII "PRAW"
    4       1     mode byte: 0=L(gray) 1=LA(grayAlpha) 2=RGB 3=RGBA 4=P(palette)
    5       4     width  (u32le)
    9       4     height (u32le)
    13      ...   [mode==4 only] paletteSize (u16le), then paletteSize * 4
                  bytes of RGBA palette entries
    ...     ...   pixel data: width*height*bytesPerPixel(mode) bytes,
                  row-major, top-to-bottom, tightly packed (no row padding)

This must match PILean's loader in `Tests/Praw.lean` byte-for-byte. See that
file's docstring for the Lean-side mirror of this format.
"""
from __future__ import annotations

import struct

MODE_L = 0
MODE_LA = 1
MODE_RGB = 2
MODE_RGBA = 3
MODE_P = 4

MODE_NAMES = {MODE_L: "l", MODE_LA: "la", MODE_RGB: "rgb", MODE_RGBA: "rgba", MODE_P: "p"}

BYTES_PER_PIXEL = {MODE_L: 1, MODE_LA: 2, MODE_RGB: 3, MODE_RGBA: 4, MODE_P: 1}

MAGIC = b"PRAW"

# Pillow mode string -> our mode code, for the common 8-bit modes that map
# 1:1 onto PILean's Mode inductive.
PIL_MODE_TO_CODE = {"L": MODE_L, "LA": MODE_LA, "RGB": MODE_RGB, "RGBA": MODE_RGBA, "P": MODE_P}


def write_praw(path, mode: int, width: int, height: int, data: bytes,
               palette: list[tuple[int, int, int, int]] | None = None) -> None:
    """Write a .praw fixture to `path`.

    `data` must already be tightly packed, row-major bytes in `mode`'s
    storage layout. `palette` is required iff `mode == MODE_P`: a list of
    `(r, g, b, a)` byte tuples, at most 65535 entries.
    """
    if mode not in BYTES_PER_PIXEL:
        raise ValueError(f"unknown praw mode {mode}")
    expected = width * height * BYTES_PER_PIXEL[mode]
    if len(data) != expected:
        raise ValueError(f"{path}: data size {len(data)} != expected {expected} "
                          f"({width}x{height} mode {mode})")
    out = bytearray()
    out += MAGIC
    out.append(mode)
    out += struct.pack("<I", width)
    out += struct.pack("<I", height)
    if mode == MODE_P:
        if palette is None:
            raise ValueError(f"{path}: mode P requires a palette")
        if len(palette) > 0xFFFF:
            raise ValueError(f"{path}: palette too large ({len(palette)} entries)")
        out += struct.pack("<H", len(palette))
        for (r, g, b, a) in palette:
            out += bytes((r, g, b, a))
    out += data
    with open(path, "wb") as f:
        f.write(bytes(out))


def read_praw(path):
    """Read a .praw fixture. Returns `(mode, width, height, data, palette)`;
    `palette` is `None` unless `mode == MODE_P`."""
    with open(path, "rb") as f:
        raw = f.read()
    if raw[:4] != MAGIC:
        raise ValueError(f"{path}: bad magic (not a .praw file)")
    mode = raw[4]
    if mode not in BYTES_PER_PIXEL:
        raise ValueError(f"{path}: unknown praw mode byte {mode}")
    width, height = struct.unpack_from("<II", raw, 5)
    pos = 13
    palette = None
    if mode == MODE_P:
        (n,) = struct.unpack_from("<H", raw, pos)
        pos += 2
        palette = []
        for i in range(n):
            r, g, b, a = raw[pos:pos + 4]
            palette.append((r, g, b, a))
            pos += 4
    bpp = BYTES_PER_PIXEL[mode]
    data = raw[pos:pos + width * height * bpp]
    return mode, width, height, data, palette


def image_to_praw_args(im):
    """Given a Pillow image already in mode L/LA/RGB/RGBA/P (8-bit storage),
    return `(mode, width, height, data, palette)` ready for `write_praw`.

    For P images the palette is folded to RGBA: `im.getpalette()` (RGB
    triples) plus per-index alpha from `im.info['transparency']`, which
    Pillow represents either as a single int (one fully-transparent index,
    all others opaque) or as a bytes/list of one alpha value per palette
    entry (see `PngImagePlugin.chunk_tRNS`). Entries with no explicit alpha
    default to fully opaque (255).
    """
    if im.mode not in PIL_MODE_TO_CODE:
        raise ValueError(f"unsupported Pillow mode {im.mode!r} for .praw")
    mode = PIL_MODE_TO_CODE[im.mode]
    w, h = im.size
    if mode == MODE_P:
        pal = im.getpalette() or []
        n = len(pal) // 3
        alphas = [255] * n
        tr = im.info.get("transparency")
        if isinstance(tr, int):
            if 0 <= tr < n:
                alphas[tr] = 0
        elif tr is not None:
            for i, a in enumerate(tr):
                if i < n:
                    alphas[i] = a
        palette = [(pal[3 * i], pal[3 * i + 1], pal[3 * i + 2], alphas[i]) for i in range(n)]
        return mode, w, h, im.tobytes(), palette
    return mode, w, h, im.tobytes(), None


def resolve_rgba(mode: int, width: int, height: int, data: bytes,
                  palette: list[tuple[int, int, int, int]] | None) -> list[tuple[int, int, int, int]]:
    """Promote every pixel to `(r, g, b, a)`, mirroring
    `PILean.Image.getPixel!`'s promotion exactly (gray -> `(v,v,v,255)`,
    grayAlpha -> `(v,v,v,a)`, rgb -> `(r,g,b,255)`, rgba as-is, palette ->
    palette lookup).

    This is the format-agnostic notion of "pixel-exact" used throughout
    PILean's own test suite (see `Tests.Framework.assertImagesEq`) and is
    what `crosscheck.py` compares — deliberately *not* raw storage bytes,
    since e.g. GIF encoders are free to renumber palette indices (Pillow's
    own GIF writer does, whenever the source palette has unused entries)
    without changing the decoded image.
    """
    out = []
    bpp = BYTES_PER_PIXEL[mode]
    for i in range(width * height):
        off = i * bpp
        if mode == MODE_L:
            v = data[off]
            out.append((v, v, v, 255))
        elif mode == MODE_LA:
            v, a = data[off], data[off + 1]
            out.append((v, v, v, a))
        elif mode == MODE_RGB:
            out.append((data[off], data[off + 1], data[off + 2], 255))
        elif mode == MODE_RGBA:
            out.append((data[off], data[off + 1], data[off + 2], data[off + 3]))
        elif mode == MODE_P:
            assert palette is not None
            out.append(palette[data[off]])
    return out
