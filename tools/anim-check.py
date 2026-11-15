# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Checks PILean's APNG and GIF writers against Python's standard library only (zlib, struct).
#
#   python3 -I tools/anim-check.py DIR    check the files `lake exe pilean-test --anim-out DIR`
#                                         wrote. Every APNG is parsed (chunk CRCs, sequence
#                                         numbers, filters) and composed; every GIF is decoded
#                                         by an LZW decoder and a canvas written here; for each
#                                         sequence of at most 256 colours the two must show the
#                                         same canvas in every frame, with the same delays and
#                                         loop count.

import struct
import sys
import zlib

def apng(path):
    d = open(path, 'rb').read()
    assert d[:8] == b'\x89PNG\r\n\x1a\n'
    pos = 8; chunks = []
    while pos < len(d):
        ln, = struct.unpack('>I', d[pos:pos+4]); ty = d[pos+4:pos+8]; data = d[pos+8:pos+8+ln]
        crc, = struct.unpack('>I', d[pos+8+ln:pos+12+ln])
        assert zlib.crc32(ty+data) & 0xffffffff == crc, ('crc', ty)
        chunks.append((ty, data)); pos += 12+ln
    assert pos == len(d) and chunks[-1][0] == b'IEND'
    W, H = struct.unpack('>II', chunks[0][1][:8]); assert chunks[0][1][8:] == bytes([8,6,0,0,0])
    nfr, loops = struct.unpack('>II', [c for c in chunks if c[0]==b'acTL'][0][1])
    seq = 0; frames = []; cur = None
    for ty, data in chunks:
        if ty == b'fcTL':
            s, w, h, x, y, dn, dd, disp, bl = struct.unpack('>IIIIIHHBB', data); assert s == seq; seq += 1
            cur = dict(w=w,h=h,x=x,y=y,dn=dn,dd=dd,disp=disp,bl=bl,z=b''); frames.append(cur)
        elif ty == b'IDAT': cur['z'] += data
        elif ty == b'fdAT':
            s, = struct.unpack('>I', data[:4]); assert s == seq; seq += 1; cur['z'] += data[4:]
    assert len(frames) == nfr
    canvas = bytearray(W*H*4); out = []
    for f in frames:
        raw = zlib.decompress(f['z']); w, h = f['w'], f['h']; rb = w*4
        assert len(raw) == h*(rb+1)
        prev = bytearray(rb); rows = []
        for r in range(h):
            ft = raw[r*(rb+1)]; cur_ = bytearray(raw[r*(rb+1)+1:(r+1)*(rb+1)])
            for i in range(rb):
                a = cur_[i-4] if i >= 4 else 0; b = prev[i]; c = prev[i-4] if i >= 4 else 0
                if ft == 1: cur_[i] = (cur_[i]+a) & 255
                elif ft == 2: cur_[i] = (cur_[i]+b) & 255
                elif ft == 3: cur_[i] = (cur_[i]+(a+b)//2) & 255
                elif ft == 4:
                    p = a+b-c; pa,pb,pc = abs(p-a),abs(p-b),abs(p-c)
                    pr = a if pa<=pb and pa<=pc else (b if pb<=pc else c)
                    cur_[i] = (cur_[i]+pr) & 255
            rows.append(cur_); prev = cur_
        assert f['bl'] == 0 and f['disp'] == 0
        for r in range(h):
            o = ((f['y']+r)*W + f['x'])*4; canvas[o:o+rb] = rows[r]
        out.append((bytes(canvas), f['dn'], f['dd']))
    return W, H, loops, out

def lzw(minc, data, n):
    clear = 1 << minc; eoi = clear+1
    table = None; size = minc+1; bits = 0; nb = 0; i = 0; out = bytearray(); prev = None
    def reset():
        return [bytes([k]) for k in range(clear)] + [b'', b'']
    table = reset()
    for byte in data:
        bits |= byte << nb; nb += 8
        while nb >= size:
            code = bits & ((1 << size)-1); bits >>= size; nb -= size
            if code == clear: table = reset(); size = minc+1; prev = None; continue
            if code == eoi: assert len(out) == n, (len(out), n); return bytes(out)
            if prev is None: entry = table[code]
            else:
                if code < len(table): entry = table[code]
                elif code == len(table): entry = prev + prev[:1]
                else: raise Exception('bad code')
                if len(table) < 4096: table.append(prev + entry[:1])
            out += entry; prev = entry
            if len(table) == (1 << size) and size < 12: size += 1
    raise Exception('no eoi')

def gif(path):
    d = open(path,'rb').read(); assert d[:6] == b'GIF89a'
    W, H, pk = struct.unpack('<HHB', d[6:11]); pos = 13
    gct = d[pos:pos+3*(1 << ((pk&7)+1))]; pos += len(gct)
    canvas = bytearray(W*H*4); out = []; gce = None; loops = 1
    while True:
        b = d[pos]
        if b == 0x3B: break
        if b == 0x21:
            lab = d[pos+1]
            if lab == 0xF9:
                f, dl, ti = struct.unpack('<BHB', d[pos+3:pos+7]); gce = (f>>2 & 7, ti if f & 1 else None, dl); pos += 8
            else:
                pos += 2; blob = b''
                while d[pos]: blob += d[pos+1:pos+1+d[pos]]; pos += 1+d[pos]
                pos += 1
                if lab == 0xFF and blob[:11] == b'NETSCAPE2.0':
                    n, = struct.unpack('<H', blob[12:14]); loops = 0 if n == 0 else n+1
        elif b == 0x2C:
            x,y,w,h,f = struct.unpack('<HHHHB', d[pos+1:pos+10]); pos += 10
            assert not f & 0x80 and not f & 0x40
            minc = d[pos]; pos += 1; blob = b''
            while d[pos]: blob += d[pos+1:pos+1+d[pos]]; assert d[pos] <= 255; pos += 1+d[pos]
            pos += 1
            ix = lzw(minc, blob, w*h)
            disp, ti, dl = gce; before = bytes(canvas)
            for r in range(h):
                for c in range(w):
                    v = ix[r*w+c]
                    if v == ti: continue
                    o = ((y+r)*W+x+c)*4; canvas[o:o+4] = bytes(gct[3*v:3*v+3]) + b'\xff'
            out.append((bytes(canvas), dl, 100))
            if disp == 2:
                for r in range(h):
                    o = ((y+r)*W+x)*4; canvas[o:o+4*w] = bytes(4*w)
            elif disp == 3: canvas = bytearray(before)
            gce = None
        else: raise Exception('bad block %x' % b)
    return W, H, loops, out


def main(base):
    for name in ["moving-square", "growing-bar", "identical-frames", "single-frame",
                 "transparent-frames", "dot-60"]:
        w, h, loops_a, a = apng(f"{base}/{name}.png")
        w2, h2, loops_g, g = gif(f"{base}/{name}.gif")
        assert (w, h) == (w2, h2) and len(a) == len(g), (name, len(a), len(g))
        assert loops_a == loops_g, name
        for (fa, dn, dd), (fg, dl, _) in zip(a, g):
            assert fa == fg, name
            assert dn * 100 == dl * dd, (name, dn, dd, dl)
        print(name, "ok:", len(a), "frames, loops", loops_a)
    for name in ["gradient", "gradient-dithered"]:
        _, _, _, g = gif(f"{base}/{name}.gif")
        print(name, "decodes:", len(g), "frames")


if __name__ == "__main__":
    main(sys.argv[1])
