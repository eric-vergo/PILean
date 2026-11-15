# PILean design

PILean is a pure-Lean image library: what Pillow is to Python, with plots, a vector canvas and
graphs of nodes and edges on top, SVG and PNG output, and a traceability layer that ties every
image to the Lean that produced it. This note gives the planned module layout, the public API in
outline, what is exact and what is floating point, and the open choices.

## Principles

1. **Pure Lean, `Init` and `Std` only.** No FFI, no Mathlib, no large dependencies. Text comes
   from LeAnTeX (fonts and layout), added as a dependency when the text layer needs it.
2. **Values first.** An image, a figure, a drawing or a graph is a Lean value; output is a
   function of it. The same value gives the same bytes on every machine (deterministic number
   formatting, stable ordering, no clocks or randomness).
3. **Untrusted input everywhere.** Labels, data, fonts and images read from files are treated as
   hostile: escaped, bounded, checked; no panics, every loop bounded by its input.
4. **Craft.** Defaults that look deliberate without tuning: whole-pixel plot areas, hairlines on
   pixel centres, a restrained colour-blind-safe palette, typographic minus signs, consistent
   margins; visual variants go to the owner before a default is fixed.

## Module layout

| Module | Contents | State |
|---|---|---|
| `PILean.Color` | `Rgba` (8-bit sRGB, straight alpha), `LinearRgba`, OKLab / OKLCH, gamut mapping, WCAG contrast, hex, `over`, `mixOk` | done |
| `PILean.Geometry` | `Point`, `Affine`, `Box` | done |
| `PILean.Path` | `PathCmd`, `Path`, shapes, `transform`, `flatten`, `bounds` | done |
| `PILean.Svg` | the SVG document model and writer | done |
| `PILean.Plot.Ticks`, `PILean.Plot.Figure` | nice ticks, the `Figure` spec and its SVG | first version |
| `PILean.Raster` | anti-aliased scanline fill (non-zero and even-odd), the stroker (joins, caps, miter limit, dashes), gradients, Porter–Duff compositing, clipping | next |
| `PILean.Image` | `Image` (mode, size, pixels in a `ByteArray`), `ImageDraw`-style operations on it, crop, paste, resize (box, bilinear, Lanczos), channel operations | next |
| `PILean.Png` | PNG writer and reader: CRC-32, Adler-32, DEFLATE (stored, fixed and dynamic Huffman; inflate with every bound checked), filters, `tEXt`/`iTXt` chunks | next |
| `PILean.Canvas` | a retained vector canvas: layers, groups, transforms, styles, text runs; rendered to SVG or through `Raster` to PNG | later |
| `PILean.Text` | text through LeAnTeX: its OpenType reader (outlines, advances, kerning, ligatures) and, later, its text and math layout; labels become outlines or SVG text | later |
| `PILean.Plot.*` | scales (linear, log, symlog, time), axes, scatter, bar, histogram, area, error bars, legends, facets; LaTeX labels through LeAnTeX | later |
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
`L`, `RGB`, `RGBA`; box coordinates; filter names); no Pillow code. `THIRD-PARTY.md` records
Pillow's MIT-CMU licence.

## Exact and floating point

- **Exact (integers, rationals):** pixel dimensions, image buffers and their indexing, PNG and
  DEFLATE (bit-exact by construction and by round-trip tests), CRC and Adler checksums,
  fingerprints, tick values (integer multiples of a step), the manifest. Data values that come
  from Lean (`Nat`, `Int`, `Rat`-like) stay exact until they are mapped to the page.
- **Floating point (`Float`, IEEE double, deterministic):** geometry, transforms, path
  flattening, the rasteriser's coverage, colour conversions, scales. These are tested against
  published values and goldens, not proved; the stated limit of the trust layer is that a figure's
  *content* (which function, which data points, which edges) is proved, its *rendering* tested.
- **Output formatting:** every number written to SVG goes through one formatter with a fixed
  number of decimals and no exponent, so output is byte-stable.

## The raster batch: what it adds to the IDE's path filler

IDEiL's `Ideil.Core.PathFill` (the owner's code) parses SVG path data, flattens to a fixed device
tolerance and computes exact per-line coverage under the non-zero rule, sampled on 16 lines per
pixel row, into an alpha mask. `PILean.Raster` builds on its approach and must add: the even-odd
rule; a stroker (round, miter and bevel joins with a miter limit; butt, round and square caps;
dashes with an offset) producing fill paths; analytic area coverage (signed area per cell, as in
font rasterisers) for exact anti-aliasing instead of sub-row sampling, or sub-rows kept with a
tolerance argument; clipping by a path; linear and radial gradients; Porter–Duff compositing in
linear light with premultiplied alpha; and bounded work for hostile paths (caps on segment count
and image size).

## Trust

Four parts, all requested by the owner:

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

## Open choices for the owner

Each has a recommendation; none blocks the next batch.

1. **Text in SVG: outlines or `<text>`.** Outlines (glyph paths from LeAnTeX's font reader) look
   the same everywhere and need no installed font, but are larger and not selectable; `<text>`
   with an embedded subset font (WOFF2 needs Brotli) is smaller and selectable.
   *Recommendation:* outlines by default for figures (exact appearance, no font licensing in each
   file beyond what the font allows), `<text>` as an option.
2. **Default text family.** New Computer Modern (the owner's choice for documents, licence under
   review) or Latin Modern for plot labels. *Recommendation:* the same family as the document
   (NewCM) once its licence is accepted; Latin Modern Sans until then.
3. **Pixel model.** Straight or premultiplied alpha in `Image`. *Recommendation:* straight alpha
   in the public `Image` (as Pillow's `RGBA`), premultiplied inside the rasteriser.
4. **Anti-aliasing.** Analytic area coverage or sub-row sampling. *Recommendation:* analytic
   coverage (exact for polygons, matches FreeType and font rendering).
5. **Default figure size and style.** 640 × 400 px with the current theme, or a print-oriented
   size in points. *Recommendation:* keep pixels as the unit and offer a few rendered style
   variants for the owner to choose from in the plots batch.
6. **Where figures live in a blueprint.** A Lean attribute (`@[figure]`) on a definition of type
   `Figure` that the site build renders, or explicit calls in the blueprint source.
   *Recommendation:* the attribute, which also gives the trust layer its source declaration.
7. **Graph layout depth.** Layered layout only, or force-directed as well. *Recommendation:*
   layered first (deterministic, suits dependency graphs), force-directed later.
