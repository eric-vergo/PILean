/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# `pilean-probe`

`pilean-probe png|gif|apng|zlib FILE` decodes the file with the reader's default limits (zlib:
an output cap of 256 MiB) and prints `ok` with the size of what was decoded, or `error` with the
reason. The test driver runs it on hostile inputs under limits (`PILeanTest.Bounds`); it imports
only the library, so what it costs is what the reader costs.
-/

open PILean

/-- Decodes the file named by the second argument as the first says. -/
def main (args : List String) : IO UInt32 := do
  let [kind, file] := args | do
    IO.eprintln "usage: pilean-probe png|gif|apng|zlib FILE"
    return 2
  let bytes ← IO.FS.readBinFile file
  let line := match kind with
    | "png" => match Png.decode bytes with
      | .ok d => s!"ok {d.image.width}x{d.image.height} {d.image.data.size}"
      | .error e => s!"error {e}"
    | "gif" => match Anim.readGif bytes with
      | .ok s => s!"ok {s.width}x{s.height} frames {s.frames.size}"
      | .error e => s!"error {repr e}"
    | "apng" => match Anim.readApng bytes with
      | .ok s => s!"ok {s.width}x{s.height} frames {s.frames.size}"
      | .error e => s!"error {repr e}"
    | _ => match Png.zlibDecompress bytes (1 <<< 28) with
      | .ok o => s!"ok {o.size}"
      | .error e => s!"error {e}"
  IO.println line
  return 0
