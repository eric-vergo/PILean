# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
#
# Writes PILean/Raster/SrgbTables.lean: the sRGB transfer function at 16-bit precision, as two
# tables of integers so that the rasteriser's colour conversions are the same on every machine:
#   * decode16[i]   = round(65535 * decode(i / 255)) for the 256 8-bit values;
#   * threshold[k]  = round(65535 * decode((k + 0.5) / 255)) for k = 0 .. 254, the linear values
#     where the nearest 8-bit encoding steps from k to k + 1.
# decode is the sRGB transfer function of IEC 61966-2-1 (threshold 0.04045, exponent 2.4).
#
# Usage, from the repository root: python3 -I tools/gen-srgb.py


def decode(x):
    """The sRGB transfer function: an encoded value in [0, 1] to linear light."""
    return x / 12.92 if x <= 0.04045 else ((x + 0.055) / 1.055) ** 2.4


def rnd(v):
    """Round half up to an integer."""
    return int(v + 0.5)


def table(name, doc, values):
    """A Lean array definition, eight values to a line."""
    lines = []
    for i in range(0, len(values), 8):
        lines.append("    " + ", ".join(str(v) for v in values[i:i + 8]))
    body = ",\n".join(lines)
    return f"/-- {doc} -/\ndef {name} : Array Nat := #[\n{body}]\n"


def main():
    """Writes the module."""
    dec = [rnd(65535 * decode(i / 255)) for i in range(256)]
    thr = [rnd(65535 * decode((k + 0.5) / 255)) for k in range(255)]
    out = f"""/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# sRGB tables

The sRGB transfer function (IEC 61966-2-1) at 16-bit precision, written by `tools/gen-srgb.py`
so that colour conversions are integer table lookups, the same on every machine.

## Main definitions

* `srgbDecode16`: an 8-bit sRGB value to linear light in `[0, 65535]`.
* `srgbThreshold16`: the linear values where the nearest 8-bit encoding steps up.
-/

namespace PILean.Raster

{table("srgbDecode16", "Linear light (0 to 65535) of each 8-bit sRGB value.", dec)}
{table("srgbThreshold16", "For `k` from 0 to 254, the linear light (0 to 65535) half way, in " +
       "encoded terms, between\\n8-bit values `k` and `k + 1`.", thr)}
end PILean.Raster
"""
    with open("PILean/Raster/SrgbTables.lean", "w", encoding="utf-8") as f:
        f.write(out.replace("\\n", "\n"))


if __name__ == "__main__":
    main()
