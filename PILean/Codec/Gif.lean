import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Compress.Lzw

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# GIF

GIF87a/89a decode (WP15) and encode including animation (WP16), on top of
`PILean.Compress.Lzw` (WP14). The `Codec` surface is single-frame; the
frame-level API (`decode`, `encodeFrames`, `saveGif`) is the real
interface. WP15 may add a lossless lower-level `GifFile` view as new defs.

Decode composites frames to RGBA honoring disposal methods 0/1/2/3
(disposal 2 restores to *transparent*, the modern interpretation, matching
Pillow). Encode v1 builds one global color table by quantizing across
frames; per-frame local tables and frame-diff optimization come later.
-/

namespace PILean.Gif

/-- GIF frame disposal method (GCE "disposal" field). -/
inductive Disposal where
  | unspecified
  | keep
  | restoreBackground
  | restorePrevious
  deriving Repr, DecidableEq, Inhabited

/-- One frame to encode: an image plus its display duration. -/
structure Frame where
  image : Image
  durationMs : Nat := 100
  deriving Inhabited

/-- Options for writing (animated) GIFs. -/
structure SaveOptions where
  /-- Number of animation loops; 0 = forever (NETSCAPE2.0 extension). -/
  loopCount : Nat := 0
  /-- Palette index rendered as transparent, if any. -/
  transparentIndex : Option UInt8 := none
  deriving Repr, Inhabited

/-- Decode all frames, composited to `.rgba`, each with its display
duration in milliseconds. -/
def decode (bytes : ByteArray) : Except DecodeError (Array (Image × Nat)) :=
  .error (.unsupported "gif" "decoder not implemented yet (WP15)")

/-- Encode frames as an (animated, if more than one frame) GIF. -/
def encodeFrames (frames : Array Frame) (opts : SaveOptions := {}) :
    Except EncodeError ByteArray :=
  .error (.invalidArg "gif encoder not implemented yet (WP16)")

/-- Write an animated GIF to a file. -/
def saveGif (path : System.FilePath) (frames : Array Frame)
    (opts : SaveOptions := {}) : IO Unit := do
  match encodeFrames frames opts with
  | .ok bytes => IO.FS.writeBinFile path bytes
  | .error e => throw (IO.userError (toString e))

/-- GIF codec (single-frame view; registered in `PILean.codecs`). -/
def codec : Codec where
  name := "gif"
  extensions := [".gif"]
  sniff := fun b =>
    b.size ≥ 6 && b.get! 0 == 71 && b.get! 1 == 73 && b.get! 2 == 70 &&
    b.get! 3 == 56 && (b.get! 4 == 55 || b.get! 4 == 57) && b.get! 5 == 97  -- GIF87a/89a
  decode := fun b => do
    let frames ← decode b
    match frames[0]? with
    | some (img, _) => return img
    | none => throw (.corrupt 0 "GIF contains no frames")
  encode := fun img => encodeFrames #[{ image := img }]

end PILean.Gif
