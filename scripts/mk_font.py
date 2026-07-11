#!/usr/bin/env python3
"""Generate PILean/Font/Spleen8x16.lean from the Spleen 8x16 BDF font.

Fetches spleen-8x16.bdf (primary: raw.githubusercontent.com master branch;
fallback: the latest GitHub release tarball), parses its BITMAP sections,
and emits a Lean source file containing a single compact hex-string literal
with one glyph per codepoint 32..255 (224 glyphs, 16 bytes each = 3584
bytes = 7168 hex chars). Codepoints the font doesn't cover (Latin-1 C1
controls, 128..159) get a blank (all-zero) glyph; these are logged below.

If neither Spleen source is reachable, falls back to the public-domain
font8x8_basic.h (ASCII 32..126 only, 8x8, bit-reversed rows since that
source stores LSB-leftmost) and emits an 8-pixel-tall font instead. If that
also fails, the script exits with a nonzero status and no file is written.

Run from the repository root: `python3 scripts/mk_font.py`.
"""

from __future__ import annotations

import io
import re
import sys
import tarfile
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
OUT_PATH = REPO_ROOT / "PILean" / "Font" / "Spleen8x16.lean"

SPLEEN_RAW_URL = "https://raw.githubusercontent.com/fcambus/spleen/master/spleen-8x16.bdf"
SPLEEN_RELEASES_API = "https://api.github.com/repos/fcambus/spleen/releases/latest"
SPLEEN_LICENSE_URL = "https://raw.githubusercontent.com/fcambus/spleen/master/LICENSE"
FONT8X8_URL = "https://raw.githubusercontent.com/dhepper/font8x8/master/font8x8_basic.h"

FIRST_CODE = 32
CODE_COUNT = 224  # 32..255 inclusive

SPLEEN_LICENSE_FALLBACK = """Copyright (c) 2018-2026, Frederic Cambus
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
"""


def fetch(url: str, timeout: int = 30) -> bytes | None:
    """Best-effort HTTP GET; returns None (and logs) on any failure."""
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "PILean-mk_font/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read()
    except Exception as exc:  # noqa: BLE001 - best-effort network fetch
        print(f"  fetch failed: {url}: {exc}", file=sys.stderr)
        return None


def fetch_spleen_bdf() -> bytes | None:
    """Try the raw master BDF first, then the latest release tarball."""
    print(f"Trying primary source: {SPLEEN_RAW_URL}")
    data = fetch(SPLEEN_RAW_URL)
    if data:
        return data

    print("Primary source failed; trying latest release tarball…")
    import json

    meta = fetch(SPLEEN_RELEASES_API)
    if not meta:
        return None
    try:
        release = json.loads(meta)
        tag = release["tag_name"]
    except Exception as exc:  # noqa: BLE001
        print(f"  couldn't parse release metadata: {exc}", file=sys.stderr)
        return None

    tarball_url = f"https://github.com/fcambus/spleen/releases/download/{tag}/spleen-{tag}.tar.gz"
    print(f"  downloading {tarball_url}")
    tar_bytes = fetch(tarball_url)
    if not tar_bytes:
        return None
    try:
        with tarfile.open(fileobj=io.BytesIO(tar_bytes), mode="r:gz") as tf:
            for member in tf.getmembers():
                if member.name.endswith("spleen-8x16.bdf") and "/cp437/" not in member.name:
                    f = tf.extractfile(member)
                    if f is not None:
                        return f.read()
    except Exception as exc:  # noqa: BLE001
        print(f"  couldn't extract tarball: {exc}", file=sys.stderr)
        return None
    return None


def parse_bdf(bdf_text: str) -> dict[int, bytes]:
    """Parse a BDF's STARTCHAR..ENDCHAR blocks into {codepoint: 16 row bytes}.

    Assumes (as Spleen's monospace BDFs guarantee) every glyph is exactly
    8 pixels wide, so each BITMAP row is exactly one hex byte with the MSB
    as the leftmost pixel — no bit-shifting needed.
    """
    glyphs: dict[int, bytes] = {}
    for block in bdf_text.split("STARTCHAR")[1:]:
        enc_match = re.search(r"^ENCODING\s+(-?\d+)", block, re.M)
        bitmap_match = re.search(r"^BITMAP\s*\n(.*?)\nENDCHAR", block, re.S | re.M)
        if not enc_match or not bitmap_match:
            continue
        enc = int(enc_match.group(1))
        if enc < 0:
            continue
        rows = [r.strip() for r in bitmap_match.group(1).strip().split("\n") if r.strip()]
        row_bytes = bytes(int(r[:2], 16) for r in rows)
        if len(row_bytes) < 16:
            row_bytes = row_bytes + bytes(16 - len(row_bytes))
        elif len(row_bytes) > 16:
            row_bytes = row_bytes[:16]
        glyphs[enc] = row_bytes
    return glyphs


def build_spleen_blob() -> tuple[bytes, list[int], str]:
    """Returns (3584-byte blob, missing codepoints, license text)."""
    bdf_bytes = fetch_spleen_bdf()
    if bdf_bytes is None:
        raise RuntimeError("could not fetch spleen-8x16.bdf from any source")
    glyphs = parse_bdf(bdf_bytes.decode("utf-8", errors="replace"))

    blank = bytes(16)
    missing: list[int] = []
    out = bytearray()
    for cp in range(FIRST_CODE, FIRST_CODE + CODE_COUNT):
        g = glyphs.get(cp)
        if g is None:
            missing.append(cp)
            out += blank
        else:
            out += g

    license_bytes = fetch(SPLEEN_LICENSE_URL)
    license_text = license_bytes.decode("utf-8") if license_bytes else SPLEEN_LICENSE_FALLBACK
    return bytes(out), missing, license_text


def parse_font8x8_basic(c_text: str) -> dict[int, bytes]:
    """Parse dhepper/font8x8's font8x8_basic.h into {codepoint: 8 row bytes},
    bit-reversing each row (that source is LSB-leftmost; PILean wants
    MSB-leftmost)."""

    def reverse_bits(b: int) -> int:
        r = 0
        for i in range(8):
            if b & (1 << i):
                r |= 1 << (7 - i)
        return r

    # Rows look like: 0x00, 0x00, ... one array initializer per codepoint,
    # in order starting at codepoint 0.
    array_match = re.search(r"font8x8_basic\[\]\s*=\s*\{(.*?)\};", c_text, re.S)
    if not array_match:
        raise RuntimeError("couldn't locate font8x8_basic[] array")
    body = array_match.group(1)
    glyph_blocks = re.findall(r"\{([^{}]*)\}", body)
    glyphs: dict[int, bytes] = {}
    for cp, block in enumerate(glyph_blocks):
        vals = re.findall(r"0[xX][0-9a-fA-F]+", block)
        row_bytes = bytes(reverse_bits(int(v, 16)) for v in vals[:8])
        if len(row_bytes) < 8:
            row_bytes = row_bytes + bytes(8 - len(row_bytes))
        glyphs[cp] = row_bytes
    return glyphs


def build_font8x8_blob() -> tuple[bytes, list[int], int, int, int]:
    """Returns (blob, missing codepoints, glyphHeight, firstCode, count)
    for the font8x8_basic.h fallback (ASCII 32..126 only)."""
    c_bytes = fetch(FONT8X8_URL)
    if c_bytes is None:
        raise RuntimeError("could not fetch font8x8_basic.h fallback")
    glyphs = parse_font8x8_basic(c_bytes.decode("utf-8", errors="replace"))

    first_code = 32
    count = 95  # 32..126 inclusive
    blank = bytes(8)
    missing: list[int] = []
    out = bytearray()
    for cp in range(first_code, first_code + count):
        g = glyphs.get(cp)
        if g is None:
            missing.append(cp)
            out += blank
        else:
            out += g
    return bytes(out), missing, 8, first_code, count


def to_hex(blob: bytes) -> str:
    return blob.hex()


def wrap_hex(hex_str: str, width: int = 100) -> str:
    lines = [hex_str[i : i + width] for i in range(0, len(hex_str), width)]
    return "\n".join(lines)


def comment_block(text: str) -> str:
    lines = text.rstrip("\n").split("\n")
    return "\n".join(f"  {line}".rstrip() for line in lines)


def emit_spleen_lean(blob: bytes, missing: list[int], license_text: str) -> str:
    hex_str = to_hex(blob)
    assert len(hex_str) == CODE_COUNT * 16 * 2, f"expected {CODE_COUNT * 16 * 2} hex chars, got {len(hex_str)}"
    missing_note = (
        f"Codepoints with no glyph in the source BDF (blank in this font): {missing}."
        if missing
        else "Every codepoint in range has a glyph."
    )
    return f'''/-
Spleen 8x16 bitmap font — embedded glyph data.

BSD-2-Clause

{comment_block(license_text)}

Source: https://github.com/fcambus/spleen (spleen-8x16.bdf)

{missing_note}
This file is generated by `scripts/mk_font.py`. Do not edit by hand —
re-run the script instead.
-/
import PILean.Font.Bitmap

namespace PILean

/-- Glyph data for `BitmapFont.spleen8x16`: {CODE_COUNT} glyphs (codepoints
{FIRST_CODE}..{FIRST_CODE + CODE_COUNT - 1}), 16 bytes each, one byte per
row, MSB = leftmost pixel. Codepoints the source font doesn't cover
(Latin-1 C1 controls) are blank. -/
private def spleen8x16Hex : String :=
"{wrap_hex(hex_str)}"

/-- The Spleen 8x16 bitmap font (BSD-2-Clause, © Frederic Cambus),
covering codepoints {FIRST_CODE}..{FIRST_CODE + CODE_COUNT - 1}. -/
def BitmapFont.spleen8x16 : BitmapFont :=
  {{ glyphWidth := 8, glyphHeight := 16, firstCode := {FIRST_CODE}, count := {CODE_COUNT}
    bitmap := hexToByteArray spleen8x16Hex }}

/-- The default bitmap font used by `Draw.text` and `Draw.textSize`:
Spleen 8x16. -/
def BitmapFont.default : BitmapFont := BitmapFont.spleen8x16

end PILean
'''


def emit_font8x8_lean(blob: bytes, missing: list[int], glyph_height: int, first_code: int, count: int) -> str:
    hex_str = to_hex(blob)
    missing_note = (
        f"Codepoints with no glyph in the source (blank in this font): {missing}."
        if missing
        else "Every codepoint in range has a glyph."
    )
    return f'''/-
font8x8_basic — public-domain 8x8 bitmap font (fallback; Spleen 8x16 was
unreachable when this file was generated).

Source: https://github.com/dhepper/font8x8 (font8x8_basic.h), public domain.
Rows were bit-reversed from the source's LSB-leftmost convention to
PILean's MSB-leftmost convention.

{missing_note}
This file is generated by `scripts/mk_font.py`. Do not edit by hand —
re-run the script instead.
-/
import PILean.Font.Bitmap

namespace PILean

/-- Glyph data for `BitmapFont.spleen8x16` (fallback: font8x8_basic): {count}
glyphs (codepoints {first_code}..{first_code + count - 1}), {glyph_height}
bytes each, one byte per row, MSB = leftmost pixel. -/
private def spleen8x16Hex : String :=
"{wrap_hex(hex_str)}"

/-- Fallback 8x8 bitmap font (public domain, font8x8_basic), covering
codepoints {first_code}..{first_code + count - 1}. Named `spleen8x16` to
match the frozen `BitmapFont.default` wiring even though Spleen itself
was unreachable when this file was generated — see the module comment. -/
def BitmapFont.spleen8x16 : BitmapFont :=
  {{ glyphWidth := 8, glyphHeight := {glyph_height}, firstCode := {first_code}, count := {count}
    bitmap := hexToByteArray spleen8x16Hex }}

/-- The default bitmap font used by `Draw.text` and `Draw.textSize`. -/
def BitmapFont.default : BitmapFont := BitmapFont.spleen8x16

end PILean
'''


def main() -> int:
    try:
        blob, missing, license_text = build_spleen_blob()
    except Exception as exc:  # noqa: BLE001
        print(f"Spleen unreachable ({exc}); trying font8x8_basic fallback…", file=sys.stderr)
        try:
            blob, missing, glyph_height, first_code, count = build_font8x8_blob()
        except Exception as exc2:  # noqa: BLE001
            print(f"FATAL: all font sources unreachable: {exc2}", file=sys.stderr)
            return 1
        lean_src = emit_font8x8_lean(blob, missing, glyph_height, first_code, count)
        OUT_PATH.write_text(lean_src)
        print(f"Wrote {OUT_PATH} using font8x8_basic FALLBACK (8x8, ASCII only).")
        print(f"Missing glyphs ({len(missing)}): {missing}")
        return 0

    lean_src = emit_spleen_lean(blob, missing, license_text)
    OUT_PATH.write_text(lean_src)
    print(f"Wrote {OUT_PATH} using Spleen 8x16.")
    print(f"Missing glyphs ({len(missing)}): {missing}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
