# Third-party material

PILean's own code is released under the Apache License 2.0 (`LICENSE`).

## Acknowledgement: Pillow

The shape of PILean's public API is inspired by [Pillow](https://python-pillow.org)'s (an `Image`
with a mode and a size, an `ImageDraw` with drawing operations, `ImageColor`-style colour
parsing). No Pillow code is used.

## Published values and methods

| PILean | What | Source |
|---|---|---|
| `PILean/Color.lean` | OKLab and OKLCH (matrices), CSS Color 4 gamut mapping, WCAG 2 contrast | Björn Ottosson's OKLab post (only the published matrices and reference values are used; no code), W3C CSS Color Module Level 4, W3C WCAG 2.2; carried over from earlier work by the same authors |
| `PILean/Style.lean` | the default palette | Masataka Okabe and Kei Ito, "Color Universal Design" (2008): six published colour values (reordered; the dark style's colours are the same hues stepped for a dark page) |
| `PILean/Plot/Ticks.lean` | the 1-2-5 nice-number rule | Paul S. Heckbert, "Nice numbers for graph labels", *Graphics Gems* (1990): the method, not code |
| `PILean/Png/*.lean` | CRC-32, Adler-32, DEFLATE and zlib, the PNG container and filters | RFC 1950, RFC 1951 and the PNG Specification (W3C, third edition; ISO/IEC 15948): written from the published specifications, no code copied |
| `PILean/Anim/*.lean` | APNG chunks and frame composition, GIF's container and LZW, median-cut quantisation, error diffusion | the APNG Specification (Mozilla, MDN), Graphics Interchange Format version 89a (CompuServe, 1990), Paul Heckbert, "Color image quantization for frame buffer display" (1982), Floyd and Steinberg, "An adaptive algorithm for spatial grey scale" (1976): written from the published descriptions, no code copied |
| `PILean/Raster/Coverage.lean` | scan conversion by signed area accumulated in cells | the published descriptions of the font-rs rasteriser (Raph Levien, 2016) and of FreeType's anti-aliasing rasteriser: the method, not code |
| `PILean/Raster/Stroke.lean`, `Canvas.lean`, `SvgRender.lean` | strokes (caps, joins, miter limit, dashes), Porter–Duff source over, SVG's rendering rules | SVG 1.1 (Second Edition), W3C, and Porter and Duff, "Compositing Digital Images" (1984): the definitions |
| `PILean/Raster/SrgbTables.lean` | the sRGB transfer function, tabulated by `tools/gen-srgb.py` | IEC 61966-2-1 |
| `PILean/Image/Ops.lean` | resampling filters (box, bilinear, Lanczos) | Ken Turkowski, "Filters for Common Resampling Tasks", *Graphics Gems* (1990), and the published definition of the Lanczos kernel: the methods, not code |

## PILean's own designs

The single-stroke lettering (`PILean/Text/Lettering*.lean`) is PILean's own design, drawn for it;
it copies no font's data.

## PILean's own test data

`PILeanTest/png/*.png` and `manifest.txt` are PILean's own files, written by
`tools/png-check.py` with Python's standard library.

