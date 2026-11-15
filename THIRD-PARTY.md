# Third-party material

PILean's own code is released under the Apache License 2.0 (`LICENSE`).

## Pillow

PILean's public API follows the shape and documented behaviour of
[Pillow](https://github.com/python-pillow/Pillow)'s API in places (an `Image` with a mode and a
size, an `ImageDraw` with drawing operations, `ImageColor`-style colour parsing; see
`docs/DESIGN.md`). No Pillow source code is copied, translated or ported: PILean takes names,
the division into modules and the behaviour the Pillow documentation describes, and implements
them independently in Lean. Pillow's licence (the MIT-CMU licence, read from its repository's
`LICENSE` file) permits use, copying, modification and distribution for any purpose provided its
notice is kept; its notice is reproduced here so that it travels with any part of PILean whose
design follows Pillow's.

```
The Python Imaging Library (PIL) is

    Copyright © 1997-2011 by Secret Labs AB
    Copyright © 1995-2011 by Fredrik Lundh and contributors

Pillow is the friendly PIL fork. It is

    Copyright © 2010 by Jeffrey 'Alex' Clark and contributors

Like PIL, Pillow is licensed under the open source MIT-CMU License:

By obtaining, using, and/or copying this software and/or its associated
documentation, you agree that you have read, understood, and will comply
with the following terms and conditions:

Permission to use, copy, modify and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appears in all copies, and that
both that copyright notice and this permission notice appear in supporting
documentation, and that the name of Secret Labs AB or the author not be
used in advertising or publicity pertaining to distribution of the software
without specific, written prior permission.

SECRET LABS AB AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS.
IN NO EVENT SHALL SECRET LABS AB OR THE AUTHOR BE LIABLE FOR ANY SPECIAL,
INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
```

## Published values and methods

| PILean | What | Source |
|---|---|---|
| `PILean/Color.lean` | OKLab and OKLCH (matrices), CSS Color 4 gamut mapping, WCAG 2 contrast | Björn Ottosson's OKLab post (only the published matrices and reference values are used; no code), W3C CSS Color Module Level 4, W3C WCAG 2.2; carried over from the IDEiL project (same authors) |
| `PILean/Plot/Figure.lean` | the default palette | Masataka Okabe and Kei Ito, "Color Universal Design" (2008): six published colour values |
| `PILean/Plot/Ticks.lean` | the 1-2-5 nice-number rule | Paul S. Heckbert, "Nice numbers for graph labels", *Graphics Gems* (1990): the method, not code |
