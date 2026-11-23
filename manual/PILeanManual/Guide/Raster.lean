/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta
import PILeanManual.Pictures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Raster Images, Writers and Readers" =>
%%%
tag := "raster"
%%%

```lean -show
namespace PILeanManual.RasterGuide
open PILean PILean.Raster
```

# Images
%%%
tag := "raster-image"
%%%

An {name}`PILean.Image` is a mode, a size and its pixels in a `ByteArray`, row by row: mode `L`
(grey), `RGB` or `RGBA` ({name}`PILean.Png.Mode`), with straight alpha as in Pillow's `RGBA`. The
operations keep Pillow's names and box conventions: {name}`PILean.Image.new`,
{name}`PILean.Image.getpixel`, {name}`PILean.Image.putpixel`, {name}`PILean.Image.crop`,
{name}`PILean.Image.paste` (with a mask), {name}`PILean.Image.convert`, the flips and quarter turns,
and {name}`PILean.Image.resize` with the filters nearest, bilinear, box and Lanczos.

```lean (name := imageEx)
def checker : Image :=
  Image.generate .l 8 8 fun x y _ => if (x / 2 + y / 2) % 2 == 0 then 255 else 0

#eval (checker.crop 2 2 6 6).width
#eval (checker.getpixel 0 0, checker.getpixel 2 0)
#eval ((checker.resize 4 4 .box).getpixel 0 0)
#eval checker.flipLeftRight.flipLeftRight.data.toList == checker.data.toList
```

```leanResult imageEx
```

Proved ({api}`PILean.Image.Proofs`): the sizes of the results of the operations, that they keep an
image well formed (its buffer has `width × height × channels` bytes,
{name}`PILean.Image.WellFormed`), and that a flip done twice is the identity
({name}`PILean.Image.flipLeftRight_flipLeftRight`); `resize` is tested.

# The Rasteriser
%%%
tag := "raster-draw"
%%%

{name}`PILean.Raster.Draw` draws filled and stroked paths into a canvas, as Pillow's `ImageDraw`
does: lines, rectangles and rounded rectangles, ellipses and arcs, polygons, any
{name}`PILean.Path` with the non-zero or even-odd rule, clipping to rectangles and paths, groups at
an opacity, and solid, linear and radial paints.

How it computes: every path is flattened, its coordinates rounded to 1/256 pixel, and from there on
everything is integer arithmetic. Each pixel's coverage is the exact area of the shape inside it,
for edges on that grid (except where two edges cross inside one pixel, the usual approximation of
both fill rules); the canvas holds premultiplied linear light at 16 bits a channel, composites
source over destination there, and converts to 8-bit sRGB with straight alpha at the end. So the
same outlines give the same coverage on every machine; the colour of a pixel also depends on its
paint (a gradient's parameter at a pixel is computed in floating point), the clips and the
compositing, and the outlines themselves are computed in floating point, where the platform's
trigonometric functions (round caps and joins, arcs) may differ in a last bit. The rasteriser is
tested, not proved: against shapes of known area, and against macOS's SVG renderer.

Strokes ({name}`PILean.Raster.Stroke`) have caps, joins, a miter limit and dashes. A Gaussian blur
of a coverage mask ({name}`PILean.Raster.Mask.blur`) and a drop shadow
({name}`PILean.Raster.Draw.dropShadow`) use integer weights computed with the basic operations
only, so they too are the same on every machine.

```lean
open PILean.Raster in
/-- Two cards with drop shadows, a dashed arc and a star filled by the even-odd rule. -/
def cards : Image := Id.run do
  let mut d := Draw.new 360 200 ⟨244, 245, 248, 255⟩
  for (x, c) in [(30, (⟨0, 114, 178, 255⟩ : Rgba)), (190, ⟨213, 94, 0, 255⟩)] do
    let card := Path.roundedRect x.toFloat 30 140 100 12
    d := d.dropShadow card 0 6 8 ⟨0, 0, 0, 90⟩
    d := d.fill card (.solid ⟨255, 255, 255, 255⟩)
    d := d.fill (Path.roundedRect x.toFloat 30 140 24 12) (.solid c)
  d := d.stroke (Path.polyline (Draw.arcPoints 40 140 320 260 200 340))
    { width := 3, dash := #[9, 6] } (.solid ⟨72, 72, 80, 255⟩)
  let star := (List.range 5).toArray.map fun i =>
    let a := 4 * 3.141592653589793 * i.toFloat / 5 - 1.5707963267948966
    (⟨180 + 34 * a.cos, 150 + 34 * a.sin⟩ : Point)
  d := d.fill (Path.polyline star |>.close) (.solid ⟨0, 158, 115, 255⟩) .evenOdd
  return d.toImage

/-- The cards, for the manual. -/
@[figure]
def cardsPicture : PILeanManual.Picture := ⟨cards⟩
```

:::figure PILeanManual.RasterGuide.cardsPicture (alt := "Two white cards with soft shadows on a pale grey background, each with a coloured band at the top, blue and orange; under them a dashed grey arc and a green five-pointed star filled by the even-odd rule.") (format := "png") (width := "360px")
:::

Plots, graphs, canvas drawings and animation frames reach the rasteriser through their SVG nodes
({name}`PILean.Raster.Svg.rasterize`), so a figure's PNG is drawn from the nodes its SVG is
written from.

# PNG
%%%
tag := "raster-png"
%%%

{name}`PILean.Image.writePng` writes grey, RGB and RGBA images with the five row filters,
DEFLATE (stored, fixed or dynamic Huffman codes with LZ77 matching) and the chunks `sRGB`, `gAMA`,
`pHYs`, `tEXt` and `iTXt` ({name}`PILean.Png.Metadata`). The CRC-32 and Adler-32 code is proved
equal to its definition ({name}`PILean.Png.crc32_eq_crc32Bits`,
{name}`PILean.Png.adler32_eq_adlerSpec`), and three facts of the zlib framing are proved; the
codec itself is tested, against Python's `zlib` and macOS's `sips`.

```lean (name := pngEx)
#eval match checker.writePng { pixelsPerMetre := Png.Metadata.dpi 144 } with
  | .ok b => match Image.readPng b with
    | .ok back => s!"{b.size} bytes; read back equal: {back.data.toList == checker.data.toList}"
    | .error e => e.toString
  | .error e => e.toString
```

```leanResult pngEx
```

# Reading Untrusted Files
%%%
tag := "raster-read"
%%%

The readers take bytes from anywhere, so they treat them as hostile: every length is checked, the
output size is capped before anything is allocated, and a damaged file ends in an error value, not
a crash. The caps are fields of the readers' `Limits`, with these defaults:

:::table +header
*
  * Reader
  * Cap
  * Default
*
  * PNG ({name}`PILean.Png.decode`, {name}`PILean.Image.readPng`)
  * `width × height` ({name}`PILean.Png.Limits.maxPixels`)
  * 2^26 pixels
*
  * PNG
  * decompressed image data plus decoded samples ({name}`PILean.Png.Limits.maxBytes`)
  * 2^29 bytes (512 MiB)
*
  * PNG
  * text entries, all chunks together: their strings and 128 bytes for each
    ({name}`PILean.Png.Limits.maxTextBytes`)
  * 2^22 bytes
*
  * APNG, GIF ({name}`PILean.Anim.readApng`, {name}`PILean.Anim.readGif`)
  * canvas `width × height` ({name}`PILean.Anim.Limits.maxPixels`)
  * 2^24 pixels
*
  * APNG, GIF
  * number of frames ({name}`PILean.Anim.Limits.maxFrames`)
  * 65535
*
  * APNG, GIF
  * all composed frames together, and any decompressed data ({name}`PILean.Anim.Limits.maxBytes`)
  * 2^28 bytes
*
  * source records ({name}`PILean.Trust.Source.read?`)
  * input ({name}`PILean.Trust.maxInput`), each value ({name}`PILean.Trust.maxField`)
  * 64 MiB, 4096 bytes
*
  * DOT ({name}`PILean.Graph.Dot.parse`)
  * bytes, items, nesting, attributes, string length ({name}`PILean.Graph.Dot.Limits`)
  * 16 MiB, 200000, 64, 128, 65536
:::

The defaults are the code's own, printed here when the manual was built:

```lean (name := limitsEx)
#eval ((({} : Png.Limits).maxPixels, ({} : Png.Limits).maxBytes, ({} : Png.Limits).maxTextBytes))
#eval ((({} : Anim.Limits).maxPixels, ({} : Anim.Limits).maxFrames, ({} : Anim.Limits).maxBytes))
#eval (Trust.maxInput, Trust.maxField)
```

```leanResult limitsEx
```

With the default limits, reading a PNG of `n` bytes holds at most: the input; its image data (at
most `n` bytes); the data of one other chunk at a time, with the strings decoded from it (`PLTE` and
`tRNS` are kept); the text entries, whose strings with 128 bytes for each entry come to at most
`Limits.maxTextBytes` (an entry over the budget is dropped and counted in `Decoded.textDropped`);
and two buffers whose sizes together are at most `Limits.maxBytes`, allocated only after the header
has been checked against the caps. Its work is linear in those sizes. The buffer of the decompressed
image data is sized from the header, after a check that the compressed data is long enough for that
size at DEFLATE's greatest ratio, and inflating stops with an error at its end; a zlib stream
decoded without an expected size (`zlibDecompress` without `expected`) is measured first, so a
stream that would expand past the cap is refused without its output being made. GIF and APNG hold
the composed frames (at most `Limits.maxBytes`, checked before each frame is decoded) and a constant
number of frame-sized buffers. These bound the buffers the readers allocate, not the memory of the
whole process. `lake test` runs the readers on hostile inputs in child processes and checks their
memory and CPU time.

```lean (name := hostileEx)
#eval match Image.readPng (ByteArray.mk #[137, 80, 78, 71, 13, 10, 26, 10, 0, 0]) with
  | .ok _ => "read"
  | .error e => e.toString
#eval match Anim.readGif "GIF89a".toUTF8 with
  | .ok _ => "read"
  | .error e => e.toString
```

```leanResult hostileEx
```

## Animated PNG and GIF
%%%
tag := "raster-anim-read"
%%%

{name}`PILean.Anim.readApng` and {name}`PILean.Anim.readGif` read an animation back as a
{name}`PILean.FrameSeq` of composed RGBA frames (APNG: every colour type, `dispose_op` and
`blend_op`; GIF: global and local tables, interlacing, disposal 0 to 3, transparency). What PILean
writes reads back exactly (a GIF when it has at most 256 colours); the tests also decode the files
with a decoder of their own written in Python and open them with macOS's `sips`, and mutated or
truncated files are rejected cleanly.

```lean (name := animReadEx)
def flash : FrameSeq :=
  { width := 2, height := 2, delays := #[(1, 10), (1, 10)], loops := 0,
    frames := #[Image.new .rgba 2 2 ⟨255, 0, 0, 255⟩, Image.new .rgba 2 2 ⟨0, 0, 255, 255⟩] }

#eval (flash.toApng.toOption.bind fun b => (Anim.readApng b).toOption).map fun s =>
  (s.frames.size, s.delays, s.frames.map (·.getpixel 0 0))
#eval (flash.toGif.toOption.bind fun b => (Anim.readGif b).toOption).map fun s =>
  (s.frames.size, s.delays)
```

```leanResult animReadEx
```
