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
| `PILean/Plot/Figure.lean` | the default palette | Masataka Okabe and Kei Ito, "Color Universal Design" (2008): six published colour values |
| `PILean/Plot/Ticks.lean` | the 1-2-5 nice-number rule | Paul S. Heckbert, "Nice numbers for graph labels", *Graphics Gems* (1990): the method, not code |
