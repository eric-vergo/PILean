# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Checks PILean's PNG codec against Python's standard library only (zlib, struct).
#
#   python3 -I tools/png-check.py scratch DIR     check the files `lake exe pilean-test
#                                                 --png-out DIR` wrote: every .zlib stream
#                                                 decompresses (Python's zlib) to its .in file;
#                                                 every .png parses (struct + zlib), unfilters
#                                                 and equals its .raw samples.
#   python3 -I tools/png-check.py sips DIR BMPDIR  compares BMP files that macOS `sips` made from
#                                                 the PNGs in DIR with the .raw samples.
#   python3 -I tools/png-check.py fixtures DIR    (re)writes the reader fixtures: small PNGs
#                                                 made here (our own files) covering every
#                                                 colour type, depth, interlacing, filter and
#                                                 zlib setting, with `manifest.txt` listing
#                                                 "file width height crc32-hex" where the CRC
#                                                 is over the expected RGBA samples.

import os
import struct
import sys
import zlib

SIGNATURE = b"\x89PNG\r\n\x1a\n"
CHANNELS = {0: 1, 2: 3, 3: 1, 4: 2, 6: 4}


def chunk(ty, data):
    """The bytes of one PNG chunk: length, type, data, CRC-32 of type and data."""
    body = ty + data
    return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)


def paeth(a, b, c):
    """The paeth predictor of the PNG specification."""
    p = a + b - c
    pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
    if pa <= pb and pa <= pc:
        return a
    return b if pb <= pc else c


def filter_row(ty, cur, prev, bpp):
    """The row `cur` filtered with filter type `ty` (prev is the previous unfiltered row)."""
    out = bytearray()
    for i, x in enumerate(cur):
        a = cur[i - bpp] if i >= bpp else 0
        b = prev[i]
        c = prev[i - bpp] if i >= bpp else 0
        pred = (0, a, b, (a + b) // 2, paeth(a, b, c))[ty]
        out.append((x - pred) & 255)
    return bytes(out)


def unfilter(data, width, height, bpp, rowbytes):
    """Reverses the filters of `height` rows of `rowbytes` bytes (each led by a type byte)."""
    rows, prev, pos = [], bytes(rowbytes), 0
    for _ in range(height):
        ty = data[pos]
        raw = data[pos + 1:pos + 1 + rowbytes]
        pos += 1 + rowbytes
        cur = bytearray()
        for i, x in enumerate(raw):
            a = cur[i - bpp] if i >= bpp else 0
            b = prev[i]
            c = prev[i - bpp] if i >= bpp else 0
            pred = (0, a, b, (a + b) // 2, paeth(a, b, c))[ty]
            cur.append((x + pred) & 255)
        rows.append(bytes(cur))
        prev = bytes(cur)
    if pos != len(data):
        raise ValueError("extra image data")
    return b"".join(rows)


def parse_png(blob):
    """Splits a PNG into (chunks, ihdr) checking the signature, lengths and every CRC."""
    assert blob[:8] == SIGNATURE, "signature"
    pos, chunks = 8, []
    while pos < len(blob):
        (length,) = struct.unpack(">I", blob[pos:pos + 4])
        ty = blob[pos + 4:pos + 8]
        data = blob[pos + 8:pos + 8 + length]
        (crc,) = struct.unpack(">I", blob[pos + 8 + length:pos + 12 + length])
        assert crc == zlib.crc32(ty + data) & 0xFFFFFFFF, "CRC of " + ty.decode()
        chunks.append((ty, data))
        pos += 12 + length
    assert chunks[0][0] == b"IHDR" and chunks[-1][0] == b"IEND", "chunk order"
    w, h, depth, ctype, comp, filt, interlace = struct.unpack(">IIBBBBB", chunks[0][1])
    return chunks, (w, h, depth, ctype, interlace)


def check_scratch(d):
    """Checks the files the Lean writer produced; returns the number of failures."""
    bad = 0
    names = sorted(os.listdir(d))
    n_z = n_p = 0
    for f in names:
        path = os.path.join(d, f)
        if f.endswith(".zlib"):
            want = open(path[:-len(f)] + f.split(".")[0] + ".in", "rb").read()
            got = zlib.decompress(open(path, "rb").read())
            ok = got == want
            n_z += 1
            if not ok:
                print("FAIL zlib", f)
                bad += 1
        elif f.endswith(".png"):
            base = path[:-4]
            raw = open(base + ".raw", "rb").read()
            w, h, mode = open(base + ".info").read().split()
            chunks, (pw, ph, depth, ctype, il) = parse_png(open(path, "rb").read())
            ch = {"l": 1, "rgb": 3, "rgba": 4}[mode]
            idat = b"".join(d_ for t, d_ in chunks if t == b"IDAT")
            data = zlib.decompress(idat)
            px = unfilter(data, pw, ph, ch, pw * ch)
            types = [t for t, _ in chunks]
            ok = (pw, ph) == (int(w), int(h)) and depth == 8 and il == 0 and px == raw
            ok = ok and CHANNELS[ctype] == ch and types[1:3] == [b"sRGB", b"gAMA"]
            ok = ok and b"tEXt" in types
            n_p += 1
            if not ok:
                print("FAIL png", f)
                bad += 1
    print("scratch: %d zlib streams, %d PNG files, %d failures" % (n_z, n_p, bad))
    return bad


def read_bmp(blob):
    """Reads an uncompressed BMP (8, 24 or 32 bits per pixel) into (w, h, bpp, rows, palette),
    rows being top-down byte strings of the pixel data without padding."""
    off, = struct.unpack("<I", blob[10:14])
    w, h, planes, bpp = struct.unpack("<iiHH", blob[18:30])
    hdr, = struct.unpack("<I", blob[14:18])
    palette = blob[14 + hdr:off]
    stride = ((w * bpp + 31) // 32) * 4
    rows = [blob[off + r * stride: off + r * stride + w * bpp // 8] for r in range(abs(h))]
    if h > 0:
        rows.reverse()
    return w, abs(h), bpp, rows, palette


def check_sips(d, bmpdir):
    """Compares BMP files that macOS `sips` made from our PNGs with the raw samples."""
    bad = n = 0
    for f in sorted(os.listdir(bmpdir)):
        if not f.endswith(".bmp"):
            continue
        base = os.path.join(d, f[:-4])
        raw = open(base + ".raw", "rb").read()
        w, h, mode = open(base + ".info").read().split()
        w, h = int(w), int(h)
        bw, bh, bpp, rows, pal = read_bmp(open(os.path.join(bmpdir, f), "rb").read())
        got = bytearray()
        for row in rows:
            if bpp == 8:
                got += bytes(pal[4 * v] for v in row)  # grey palette: blue entry
            elif bpp == 24:
                for i in range(0, len(row), 3):
                    got += bytes((row[i + 2], row[i + 1], row[i]))
            else:
                for i in range(0, len(row), 4):
                    got += bytes((row[i + 2], row[i + 1], row[i], row[i + 3]))
        if mode == "rgba" and bpp == 24:
            want = b"".join(raw[4 * i:4 * i + 3] for i in range(w * h))
        elif mode == "l" and bpp == 24:
            want = b"".join(bytes((v, v, v)) for v in raw)
        else:
            want = raw
        n += 1
        if (bw, bh) != (w, h) or bytes(got) != want:
            print("FAIL sips", f, "bpp", bpp)
            bad += 1
    print("sips: %d BMP files compared, %d failures" % (n, bad))
    return bad


class Fix:
    """One reader fixture: how to encode it and what the reader must return."""

    def __init__(self, name, w, h, ctype, depth, pixels, **kw):
        self.name, self.w, self.h, self.ctype, self.depth = name, w, h, ctype, depth
        self.pixels = pixels  # pixels[y][x] = tuple of samples at `depth`
        self.plte = kw.get("plte")
        self.trns = kw.get("trns")
        self.interlace = kw.get("interlace", 0)
        self.filters = kw.get("filters", "mixed")
        self.level = kw.get("level", 6)
        self.strategy = kw.get("strategy", zlib.Z_DEFAULT_STRATEGY)
        self.split = kw.get("split", 0)
        self.extra = kw.get("extra", [])


def pack_row(samples, depth):
    """Packs a row of samples (flat list) at `depth` bits each into bytes."""
    if depth == 8:
        return bytes(samples)
    if depth == 16:
        return b"".join(struct.pack(">H", s) for s in samples)
    bits = "".join(format(s, "0%db" % depth) for s in samples)
    bits += "0" * (-len(bits) % 8)
    return bytes(int(bits[i:i + 8], 2) for i in range(0, len(bits), 8))


ADAM7 = [(0, 0, 8, 8), (4, 0, 8, 8), (0, 4, 4, 8), (2, 0, 4, 4), (0, 2, 2, 4), (1, 0, 2, 2),
         (0, 1, 1, 2)]


def image_data(fx):
    """The filtered, uncompressed image data of a fixture (all passes if interlaced)."""
    ch = CHANNELS[fx.ctype]
    bpp = max(1, (ch * fx.depth + 7) // 8)
    passes = ADAM7 if fx.interlace else [(0, 0, 1, 1)]
    out, counter = bytearray(), 0
    for (x0, y0, dx, dy) in passes:
        ys = range(y0, fx.h, dy)
        xs = range(x0, fx.w, dx)
        if not len(ys) or not len(xs):
            continue
        prev = None
        for y in ys:
            flat = [s for x in xs for s in fx.pixels[y][x]]
            row = pack_row(flat, fx.depth)
            if prev is None:
                prev = bytes(len(row))
            ty = counter % 5 if fx.filters == "mixed" else fx.filters
            counter += 1
            out.append(ty)
            out += filter_row(ty, row, prev, bpp)
            prev = row
    return bytes(out)


def expected_rgba(fx):
    """The RGBA samples the reader must return for a fixture (rules of PILean's reader)."""
    out = bytearray()
    for y in range(fx.h):
        for x in range(fx.w):
            p = fx.pixels[y][x]
            d = fx.depth

            def to8(v):
                return v >> 8 if d == 16 else v if d == 8 else v * 255 // ((1 << d) - 1)
            t = fx.ctype
            if t == 0:
                g = to8(p[0])
                a = 255
                if fx.trns is not None and p[0] == (fx.trns[0] & ((1 << d) - 1)):
                    a = 0
                out += bytes((g, g, g, a))
            elif t == 2:
                a = 255
                if fx.trns is not None and tuple(p) == tuple(k & ((1 << d) - 1) for k in fx.trns):
                    a = 0
                out += bytes((to8(p[0]), to8(p[1]), to8(p[2]), a))
            elif t == 3:
                r, g, b = fx.plte[p[0]]
                a = fx.trns[p[0]] if fx.trns is not None and p[0] < len(fx.trns) else 255
                out += bytes((r, g, b, a))
            elif t == 4:
                g = to8(p[0])
                out += bytes((g, g, g, to8(p[1])))
            else:
                out += bytes(to8(v) for v in p)
    return bytes(out)


def encode(fx):
    """The PNG file of a fixture."""
    out = SIGNATURE
    out += chunk(b"IHDR", struct.pack(">IIBBBBB", fx.w, fx.h, fx.depth, fx.ctype, 0, 0, fx.interlace))
    for ty, data in fx.extra:
        out += chunk(ty, data)
    if fx.plte is not None:
        out += chunk(b"PLTE", b"".join(bytes(c) for c in fx.plte))
    if fx.trns is not None:
        if fx.ctype == 3:
            out += chunk(b"tRNS", bytes(fx.trns))
        else:
            out += chunk(b"tRNS", b"".join(struct.pack(">H", k) for k in fx.trns))
    c = zlib.compressobj(fx.level, zlib.DEFLATED, 15, 8, fx.strategy)
    z = c.compress(image_data(fx)) + c.flush()
    if fx.split:
        for i in range(0, len(z), fx.split):
            out += chunk(b"IDAT", z[i:i + fx.split])
    else:
        out += chunk(b"IDAT", z)
    return out + chunk(b"IEND", b"")


def lcg(seed):
    """A small deterministic generator of 24-bit numbers."""
    s = seed
    while True:
        s = (s * 1664525 + 1013904223) & 0xFFFFFFFF
        yield s >> 8


def make_pixels(w, h, ch, depth, seed, maxval=None):
    """Pseudo-random pixels: pixels[y][x] is a tuple of `ch` samples below 2**depth."""
    g = lcg(seed)
    m = maxval if maxval is not None else (1 << depth)
    return [[tuple(next(g) % m for _ in range(ch)) for _ in range(w)] for _ in range(h)]


def fixtures():
    """The list of fixtures."""
    fs = []
    palette = [((i * 37) % 256, (i * 91 + 5) % 256, (i * 13 + 200) % 256) for i in range(256)]
    for d in (1, 2, 4, 8, 16):
        fs.append(Fix("grey%d" % d, 7, 5, 0, d, make_pixels(7, 5, 1, d, d)))
    fs.append(Fix("grey8-1x1", 1, 1, 0, 8, [[(77,)]]))
    fs.append(Fix("grey8-trns", 6, 4, 0, 8, make_pixels(6, 4, 1, 8, 3, 4), trns=[2]))
    fs.append(Fix("grey16-trns", 5, 3, 0, 16, [[(1000,), (258,), (2,), (258,), (0,)]] * 3,
                  trns=[258]))
    fs.append(Fix("grey2-trns", 9, 3, 0, 2, make_pixels(9, 3, 1, 2, 4), trns=[1]))
    for d in (8, 16):
        fs.append(Fix("rgb%d" % d, 6, 5, 2, d, make_pixels(6, 5, 3, d, 10 + d)))
    fs.append(Fix("rgb8-trns", 4, 4, 2, 8, make_pixels(4, 4, 3, 8, 5, 2), trns=[1, 0, 1]))
    fs.append(Fix("rgb16-trns", 3, 3, 2, 16,
                  [[(1, 2, 3), (4, 5, 6), (1, 2, 3)]] * 3, trns=[1, 2, 3]))
    for d in (1, 2, 4, 8):
        n = min(1 << d, 256)
        fs.append(Fix("pal%d" % d, 9, 4, 3, d, make_pixels(9, 4, 1, d, 20 + d), plte=palette[:n]))
    fs.append(Fix("pal4-trns", 9, 4, 3, 4, make_pixels(9, 4, 1, 4, 30), plte=palette[:16],
                  trns=[0, 128, 255]))
    fs.append(Fix("pal8-trns", 12, 4, 3, 8, make_pixels(12, 4, 1, 8, 31, 100), plte=palette[:100],
                  trns=list(range(0, 200, 2))))
    for d in (8, 16):
        fs.append(Fix("greyalpha%d" % d, 6, 4, 4, d, make_pixels(6, 4, 2, d, 40 + d)))
        fs.append(Fix("rgba%d" % d, 5, 6, 6, d, make_pixels(5, 6, 4, d, 50 + d)))
    for il_name, (w, h) in (("9x7", (9, 7)), ("1x1", (1, 1)), ("3x2", (3, 2)), ("17x13", (17, 13))):
        fs.append(Fix("adam7-rgb8-" + il_name, w, h, 2, 8, make_pixels(w, h, 3, 8, 60), interlace=1))
    fs.append(Fix("adam7-grey4", 11, 9, 0, 4, make_pixels(11, 9, 1, 4, 61), interlace=1))
    fs.append(Fix("adam7-grey1", 10, 6, 0, 1, make_pixels(10, 6, 1, 1, 62), interlace=1))
    fs.append(Fix("adam7-rgba16", 8, 8, 6, 16, make_pixels(8, 8, 4, 16, 63), interlace=1))
    fs.append(Fix("adam7-pal2", 7, 7, 3, 2, make_pixels(7, 7, 1, 2, 64), plte=palette[:4],
                  interlace=1))
    fs.append(Fix("adam7-rgba8", 13, 5, 6, 8, make_pixels(13, 5, 4, 8, 65), interlace=1))
    for lv in (0, 1, 9):
        fs.append(Fix("zlib-level%d" % lv, 20, 10, 6, 8, make_pixels(20, 10, 4, 8, 70, 4),
                      level=lv))
    for nm, st in (("huffman", zlib.Z_HUFFMAN_ONLY), ("rle", zlib.Z_RLE), ("fixed", zlib.Z_FIXED)):
        fs.append(Fix("zlib-" + nm, 20, 10, 6, 8, make_pixels(20, 10, 4, 8, 71, 6), strategy=st))
    fs.append(Fix("idat-split", 20, 10, 2, 8, make_pixels(20, 10, 3, 8, 72), split=7))
    for t in range(5):
        fs.append(Fix("filter%d-rgb8" % t, 12, 6, 2, 8, make_pixels(12, 6, 3, 8, 80 + t),
                      filters=t))
    fs.append(Fix("filter4-grey4", 13, 5, 0, 4, make_pixels(13, 5, 1, 4, 90), filters=4))
    fs.append(Fix("filter3-rgba16", 5, 5, 6, 16, make_pixels(5, 5, 4, 16, 91), filters=3))
    z = zlib.compress(b"Hello zTXt")
    fs.append(Fix("chunks-ancillary", 4, 4, 2, 8, make_pixels(4, 4, 3, 8, 95), extra=[
        (b"sRGB", b"\x00"), (b"gAMA", struct.pack(">I", 45455)),
        (b"tEXt", b"Title\x00Fixture"), (b"zTXt", b"Comment\x00\x00" + z),
        (b"iTXt", b"Note\x00\x00\x00en\x00Note\x00caf\xc3\xa9"),
        (b"prVt", b"private ancillary data"), (b"pHYs", struct.pack(">IIB", 2835, 2835, 1))]))
    return fs


def write_fixtures(d):
    """Writes the fixtures and the manifest into directory `d`."""
    os.makedirs(d, exist_ok=True)
    lines = []
    for fx in fixtures():
        name = fx.name + ".png"
        open(os.path.join(d, name), "wb").write(encode(fx))
        crc = zlib.crc32(expected_rgba(fx)) & 0xFFFFFFFF
        lines.append("%s %d %d %x" % (name, fx.w, fx.h, crc))
    open(os.path.join(d, "manifest.txt"), "w").write("\n".join(lines) + "\n")
    print("wrote %d fixtures to %s" % (len(lines), d))


def main():
    """Command line entry point."""
    if len(sys.argv) == 3 and sys.argv[1] == "scratch":
        sys.exit(1 if check_scratch(sys.argv[2]) else 0)
    if len(sys.argv) == 4 and sys.argv[1] == "sips":
        sys.exit(1 if check_sips(sys.argv[2], sys.argv[3]) else 0)
    if len(sys.argv) == 3 and sys.argv[1] == "fixtures":
        write_fixtures(sys.argv[2])
        return
    print("usage: png-check.py scratch DIR | sips DIR BMPDIR | fixtures DIR")
    sys.exit(2)


if __name__ == "__main__":
    main()
