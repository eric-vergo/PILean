import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Drawing primitives

Plain functions `Image → Image` — no draw-context object. Chaining
(`img |> Draw.line .. |> Draw.rect ..`) passes the image linearly through
each call, so every primitive hits the in-place `set!` fast path.

All primitives are **total** and **clip silently** (they build on
`Image.putPixel`'s out-of-bounds no-op). WP5 implements: Bresenham lines
(with width via perpendicular offsets or stamped discs), midpoint
ellipses, scanline polygon fill.
-/

namespace PILean.Draw

open PILean

/-- Set a single pixel (clipped). -/
def point (img : Image) (p : Point) (color : Color) : Image :=
  panic! "PILean.Draw.point: not implemented yet (WP5)"

/-- Draw a line segment from `a` to `b` (clipped). -/
def line (img : Image) (a b : Point) (color : Color) (width : Nat := 1) : Image :=
  panic! "PILean.Draw.line: not implemented yet (WP5)"

/-- Draw a rectangle: filled with `fill` if given, outlined with `outline`
(stroke width `width`, drawn inward from the boundary) if given. `r` is
half-open as always. -/
def rect (img : Image) (r : Rect) (fill : Option Color := none)
    (outline : Option Color := none) (width : Nat := 1) : Image :=
  panic! "PILean.Draw.rect: not implemented yet (WP5)"

/-- Draw the ellipse inscribed in `bounds` (filled and/or outlined). -/
def ellipse (img : Image) (bounds : Rect) (fill : Option Color := none)
    (outline : Option Color := none) (width : Nat := 1) : Image :=
  panic! "PILean.Draw.ellipse: not implemented yet (WP5)"

/-- Draw a polygon through `pts` (closed automatically; filled via scanline
fill and/or outlined). -/
def polygon (img : Image) (pts : Array Point) (fill : Option Color := none)
    (outline : Option Color := none) : Image :=
  panic! "PILean.Draw.polygon: not implemented yet (WP5)"

/-- Flood-fill the connected region of `seed`'s color with `color`
(4-connectivity). No-op if `seed` is out of bounds. -/
def floodFill (img : Image) (seed : Point) (color : Color) : Image :=
  panic! "PILean.Draw.floodFill: not implemented yet (WP5)"

end PILean.Draw
