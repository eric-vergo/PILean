/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

open PILean PILean.Plot PILean.Raster

/-- The sine and the cosine on [-3.14, 3.14]. -/
def trig : Figure where
  title := "Trigonometric functions"
  panels := #[{
    x := { label := "x" }, y := { label := "y" },
    series := #[.function "sin x" Float.sin (-3.14) 3.14,
      .function "cos x" Float.cos (-3.14) 3.14] }]

/-- A bar, a line and an ellipse, drawn pixel by pixel. -/
def banner : Image :=
  let d := Draw.new 300 200
  let d := d.rectangle 20 20 280 60 (fill := some (.linear ⟨20, 0⟩ ⟨280, 0⟩
    #[⟨0, ⟨230, 30, 30, 255⟩⟩, ⟨1, ⟨20, 60, 220, 255⟩⟩]))
  let d := d.line #[⟨20, 100⟩, ⟨120, 160⟩, ⟨200, 90⟩] (.solid ⟨0, 0, 0, 255⟩) 6
    .round .round
  let d := d.ellipse 220 110 280 170 (fill := some (.solid ⟨0, 158, 115, 255⟩))
  d.toImage

/-- Writes `trig.svg`, `trig-dark.svg`, `trig.png` and `banner.png` into the current folder;
exit status 1 if a picture cannot be drawn as PNG. -/
def main : IO UInt32 := do
  IO.FS.writeFile "trig.svg" trig.toSvg
  IO.FS.writeFile "trig-dark.svg" { trig with style := Style.dark }.toSvg
  let some png := trig.toPng
    | IO.eprintln "the figure could not be drawn as PNG"; return 1
  IO.FS.writeBinFile "trig.png" png
  match banner.writePng with
  | .ok bytes => IO.FS.writeBinFile "banner.png" bytes; return 0
  | .error e => IO.eprintln e.toString; return 1
