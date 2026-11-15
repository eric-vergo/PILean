# PILean design

PILean is a pure-Lean image library: what Pillow is to Python, with plots, a vector canvas and
graphs of nodes and edges on top, SVG and PNG output, and a traceability layer that ties every
image to the Lean that produced it. This note gives the planned module layout, the public API in
outline, what is exact and what is floating point, and the open choices.

## Principles

1. **Pure Lean, `Init` and `Std` only.** No FFI, no Mathlib, no large dependencies. Text will
   come from a companion typesetting library (fonts and layout; not yet public), added as a
   dependency once it is published.
2. **Values first.** An image, a figure, a drawing or a graph is a Lean value; output is a
   function of it. The same value gives the same bytes on every machine (deterministic number
   formatting, stable ordering, no clocks or randomness).
3. **Untrusted input everywhere.** Labels, data, fonts and images read from files are treated as
   hostile: escaped, bounded, checked; no panics, every loop bounded by its input.
4. **Craft.** Defaults that look deliberate without tuning: whole-pixel plot areas, hairlines on
   pixel centres, a restrained colour-blind-safe palette, typographic minus signs, consistent
   margins; visual variants are compared side by side before a default is fixed.

## Module layout

| Module | Contents | State |
|---|---|---|
| `PILean.Color` | `Rgba` (8-bit sRGB, straight alpha), `LinearRgba`, OKLab / OKLCH, gamut mapping, WCAG contrast, hex, `over`, `mixOk` | done |
| `PILean.Geometry` | `Point`, `Affine`, `Box` | done |
| `PILean.Path` | `PathCmd`, `Path`, shapes, `transform`, `flatten`, `bounds` | done |
| `PILean.Svg` | the SVG document model and writer | done |
| `PILean.Plot.Ticks`, `PILean.Plot.Figure` | nice ticks, the `Figure` spec and its SVG | first version |
| `PILean.Raster` | anti-aliased scanline fill by area coverage in integers (non-zero and even-odd), clipping to rectangles and paths, the stroker (joins, caps, miter limit, dashes), gradients, compositing in linear light, group opacity, `Draw` (in the spirit of `ImageDraw`), SVG nodes drawn | done |
| `PILean.Image` | `Image` (mode, size, pixels in a `ByteArray`), `getpixel`, `putpixel`, crop, paste with a mask, convert, flips and quarter turns, resize (nearest, bilinear, box, Lanczos) | done |
| `PILean.Png` | PNG writer and reader: CRC-32, Adler-32, DEFLATE (stored, fixed and dynamic Huffman; inflate with every bound checked), filters, `tEXt`/`iTXt`/`zTXt`, `sRGB`, `gAMA`; the reader takes every colour type and depth and Adam7 (the writer does not interlace) | done |
| `PILean.Canvas` | a retained vector canvas: layers, groups, transforms, styles, text runs; rendered to SVG or through `Raster` to PNG | later |
| `PILean.Text` | text through the companion typesetting library: its OpenType reader (outlines, advances, kerning, ligatures) and, later, its text and math layout; labels become outlines or SVG text | later |
| `PILean.Plot.*` | scales (linear, log, symlog, time), axes, scatter, bar, histogram, area, error bars, legends, facets; LaTeX labels through the companion typesetting library | later |
| `PILean.Graph` | nodes and edges, a layered (Sugiyama) layout, edge routing with splines, labels | later |
| `PILean.Trust` | source links, fingerprints, manifests and their checker, and the theorems that tie a figure to its Lean object | later |

## Public API in Pillow's spirit

Pillow's module split and verbs are familiar, so PILean keeps them where they fit, in Lean
idiom (values instead of mutation; `IO` only at the edges):

```lean
-- Image (Pillow: Image.new, Image.open, im.save, im.crop, im.resize, im.paste)
def Image.new (mode : Mode) (w h : Nat) (fill : Rgba) : Image
def Image.readPng (bytes : ByteArray) : Except PngError Image
def Image.writePng (im : Image) (meta : Metadata := {}) : ByteArray
def Image.crop (im : Image) (box : IntBox) : Image
def Image.resize (im : Image) (w h : Nat) (filter : Filter := .lanczos) : Image
def Image.paste (dst src : Image) (at : Nat × Nat) (mask : Option Image := none) : Image

-- ImageDraw (Pillow: draw.line, draw.rectangle, draw.ellipse, draw.polygon, draw.text)
def Draw.line (pts : Array Point) (stroke : Stroke) : Draw → Draw
def Draw.path (p : Path) (fill : Option Paint) (stroke : Option Stroke) : Draw → Draw
def Draw.text (at : Point) (s : String) (font : Font) (fill : Rgba) : Draw → Draw
def Draw.toImage (d : Draw) (w h : Nat) : Image        -- through Raster
def Draw.toSvg (d : Draw) (w h : Float) : String

-- ImageColor (Pillow: ImageColor.getrgb)
def Rgba.ofHex? (s : String) : Option Rgba             -- done
```

What PILean takes from Pillow is the shape of the API and its documented behaviour (modes such as
`L`, `RGB`, `RGBA`; box coordinates; filter names); no Pillow code (`THIRD-PARTY.md`).

## Exact and floating point

- **Exact (integers, rationals):** pixel dimensions, image buffers and their indexing, PNG and
  DEFLATE (bit-exact by construction and by round-trip tests), CRC and Adler checksums,
  fingerprints, tick values (integer multiples of a step), the manifest. Data values that come
  from Lean (`Nat`, `Int`, `Rat`-like) stay exact until they are mapped to the page.
- **Integers in the rasteriser:** coordinates are rounded to 1/256 pixel and everything after
  that is integer arithmetic: the cells and their areas, the coverage, compositing (16 bits a
  channel, premultiplied, in linear light) and the sRGB conversions (two tables of integers,
  `PILean/Raster/SrgbTables.lean`, written by `tools/gen-srgb.py`). The coverage is exact area
  coverage for edges on that grid, except where two edges cross inside one pixel (the usual
  approximation of both fill rules).
- **Floating point (`Float`, IEEE double):** geometry, transforms, path flattening, the
  conversion of coordinates to the 1/256 grid, a gradient's parameter at a pixel, stroke
  offsets, the weights of the bilinear and Lanczos filters, scales. The basic operations
  (`+ − × ÷ √`) are correctly rounded by IEEE 754 and so the same everywhere; the trigonometric
  functions (round caps and joins, arcs, Lanczos) come from the platform's library and may differ
  in the last bit between platforms, which moves a point by far less than the 1/256 pixel it is
  rounded to. These parts are tested against published values and goldens, not proved; the
  stated limit of the trust layer is that a figure's *content* (which function, which data
  points, which edges) is proved, its *rendering* tested.
- **Output formatting:** every number written to SVG goes through one formatter with a fixed
  number of decimals and no exponent, so output is byte-stable.

## The rasteriser

`PILean.Raster` draws paths by area coverage (`Raster/Coverage.lean` has the method): every edge
is cut at the pixel grid into pieces that add their winding (*cover*) and the area left of them
to their cell; a sweep along each row gives each pixel's winding area, which the non-zero rule
clamps to one pixel and the even-odd rule folds. Work is bounded by the image and the edges
(rows outside the image are not visited, edges left of it become vertical, right of it are
dropped), and inputs with more than four million points are refused. Strokes are the union of
one rectangle per segment, joins (miter within the limit, else bevel; round as a sector) and caps
(round as half discs), all wound the same way so that their non-zero fill has no seams; dashes
cut the flattened path first. The canvas keeps premultiplied linear light at 16 bits a channel,
composites source over destination there, and converts to 8-bit sRGB with straight alpha at
the end (the pixel model: straight alpha in `Image`, premultiplied inside). A group is drawn on
a layer of its own and composited at its opacity.

`Svg.rasterize` draws PILean's SVG nodes with it, so one description of a picture gives both
files: a figure's PNG is drawn from the nodes its SVG is written from. Measured against macOS's
SVG renderer (`tools/compare-render.py`, `sips`), the gallery's PNGs differ by 0.01 to 0.05
levels on average when PILean mixes colours as that renderer does (in sRGB); in linear light,
PILean's default, anti-aliased edges and overlaps come out lighter or darker by design.

Gradients interpolate in linear light. SVG interpolates in sRGB (its `color-interpolation`
attribute is not implemented for gradients by browsers), so PILean writes a gradient to SVG with
sixteen stops per segment sampled from its own interpolation (`gradientNode`), and both outputs
show the same colours (0.3 levels on average in the comparison).

The figure of a 2000 × 1200 function plot: drawing 244 ms, conversion to an 8-bit image 87 ms,
PNG encoding 689 ms (one core of an Apple M2 Ultra, under load; `lake exe pilean-test --bench`).
PNG encoding dominates (LZ77 matching and Huffman coding at level 6); drawing is dominated by the
full-image background and the canvas's 16-bit stores.

## Trust

Four parts:

1. **Source.** Every image records the Lean file and declaration that built it: SVG `<metadata>`
   (and a `data-source` attribute on the root), a PNG `iTXt` chunk; galleries show a "Source"
   link beside each image.
2. **Built by the build.** Images in a published site are produced only by the site build, never
   committed by hand; the manifest makes a hand edit detectable.
3. **Fingerprint.** A SHA-256 (pure Lean) of the figure specification's canonical encoding and of
   the source declaration's text, written into the file and into a manifest; a checker
   re-renders and compares.
4. **Theorems.** A `Figure` holds the Lean objects it shows (the function, the data term, the
   relation of a graph), and the renderer's sampling and drawing functions are stated over them:
   the plotted function is the definition; each data point is the evaluated term; each drawn edge
   is in the declared relation and every related pair is drawn. Statements first, proofs second,
   about the functions the code calls.

## Open design questions

Each question has a current default, which the code follows until the question is settled.

1. **Text in SVG: outlines or `<text>`.** Outlines (glyph paths from a font reader) look the same
   everywhere and need no installed font, but are larger and not selectable; `<text>` with an
   embedded subset font (WOFF2 needs Brotli) is smaller and selectable. *Default:* outlines for
   figures (exact appearance), `<text>` as an option.
2. **Default text family.** New Computer Modern or Latin Modern for plot labels. *Default:* Latin
   Modern Sans.
3. **Pixel model.** Straight or premultiplied alpha in `Image`. *Default:* straight alpha in the
   public `Image` (as Pillow's `RGBA`), premultiplied inside the rasteriser.
4. **Anti-aliasing.** Analytic area coverage or sub-row sampling. *Default:* analytic coverage
   (exact for polygons, as in font rasterisers).
5. **Default figure size and style.** 640 × 400 px, or a print-oriented size in points.
   *Default:* pixels as the unit; style variants to be compared side by side.
6. **Where figures live in a blueprint.** A Lean attribute (`@[figure]`) on a definition of type
   `Figure` that the site build renders, or explicit calls in the blueprint source. *Default:* the
   attribute, which also gives the trust layer its source declaration.
7. **Graph layout depth.** Layered layout only, or force-directed as well. *Default:* layered
   first (deterministic, suits dependency graphs), force-directed later.
