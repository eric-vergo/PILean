import PILean.Core.Error
import PILean.Core.Image

/-!
# The codec interface

Every file format implements one `Codec` value (e.g. `PILean.Png.codec`).
The registry in `PILean.IO` dispatches by content sniffing with file
extension as tiebreaker. Formats with encode options additionally expose
`<Format>.encodeWith : <Format>.Options → Image → …`; the `Codec.encode`
field always uses format defaults.
-/

namespace PILean

/-- A file-format codec. `sniff` is a cheap magic-bytes check on a prefix of
the input; `decode`/`encode` are pure and never panic on input data. -/
structure Codec where
  /-- Lowercase format name, e.g. `"png"`. -/
  name : String
  /-- Recognized file extensions including the dot, lowercase, e.g. `[".png"]`. -/
  extensions : List String
  /-- Does the input begin with this format's magic bytes? -/
  sniff : ByteArray → Bool
  decode : ByteArray → Except DecodeError Image
  encode : Image → Except EncodeError ByteArray

end PILean
