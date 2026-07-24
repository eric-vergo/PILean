import PILean.Codec.Types
import PILean.Codec.Netpbm
import PILean.Codec.Bmp
import PILean.Codec.Qoi
import PILean.Codec.Png
import PILean.Codec.Gif
import PILean.Codec.Jpeg
import PILean.Codec.Tiff

/-!
# Loading and saving

Format dispatch: content sniffing (magic bytes) first, file extension as
tiebreaker. `open` is a Lean keyword, so the loading entry point is
`Image.load`.
-/

namespace PILean

/-- All built-in codecs, in sniffing order. Static — no mutable registry. -/
def codecs : List Codec :=
  [Png.codec, Jpeg.codec, Gif.codec, Bmp.codec, Tiff.codec, Qoi.codec, Netpbm.codec]

/-- The codec registered for a file extension (with or without the dot,
case-insensitive). -/
def Codec.forExtension? (ext : String) : Option Codec :=
  let e := ext.toLower
  let e := if e.startsWith "." then e else "." ++ e
  codecs.find? fun c => c.extensions.contains e

/-- Decode from bytes, choosing the codec by content sniffing. -/
def Image.decodeAuto (bytes : ByteArray) : Except DecodeError Image :=
  match codecs.find? fun c => c.sniff bytes with
  | some c => c.decode bytes
  | none => .error .unknownFormat

private def ofDecode (r : Except DecodeError α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"PILean: {e}")

/-- Read and decode an image file. Codec chosen by content sniffing, then
by extension as a fallback. -/
def Image.load (path : System.FilePath) : IO Image := do
  let bytes ← IO.FS.readBinFile path
  match codecs.find? fun c => c.sniff bytes with
  | some c => ofDecode (c.decode bytes)
  | none =>
    match path.extension.bind Codec.forExtension? with
    | some c => ofDecode (c.decode bytes)
    | none => throw (IO.userError s!"PILean: {DecodeError.unknownFormat}")

/-- Encode and write an image file. The format comes from `format?` (a
codec name like `"png"`) or else the file extension. -/
def Image.save (img : Image) (path : System.FilePath)
    (format? : Option String := none) : IO Unit := do
  let codec? := match format? with
    | some f => codecs.find? fun (c : Codec) => c.name == f.toLower
    | none => path.extension.bind Codec.forExtension?
  match codec? with
  | some c =>
    match c.encode img with
    | .ok bytes => IO.FS.writeBinFile path bytes
    | .error e => throw (IO.userError s!"PILean: {e}")
  | none => throw (IO.userError s!"PILean: no codec for '{path}'")

/-- Write the image to a temporary PNG file and open it with the operating
system's default viewer (macOS `open`, Windows `start`, otherwise
`xdg-open`) — the PILean equivalent of PIL's `im.show()`, for interactive
visual debugging. Returns the temp-file path (the file is not cleaned up,
matching PIL). -/
def Image.show (img : Image) : IO System.FilePath := do
  let tmpBase := (← IO.getEnv "TMPDIR").getD
    (if System.Platform.isWindows then "." else "/tmp")
  let stamp ← IO.monoNanosNow
  let path : System.FilePath := System.FilePath.mk tmpBase / s!"pilean-{stamp}.png"
  img.save path
  let (cmd, args) :=
    if System.Platform.isOSX then ("open", #[path.toString])
    else if System.Platform.isWindows then ("cmd", #["/c", "start", "", path.toString])
    else ("xdg-open", #[path.toString])
  let _ ← IO.Process.spawn { cmd, args }
  return path

end PILean
