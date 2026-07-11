import PILean.Codec.Png.Chunk
import PILean.Codec.Png.Filter
import PILean.Codec.Png.Interlace
import PILean.Codec.Png.Decode
import PILean.Codec.Png.Encode

/-!
# PNG

The flagship format. Submodules: chunk layer, scanline filters, Adam7
deinterlacing, decode (WP12), encode (WP11).
-/

namespace PILean.Png

/-- PNG codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "png"
  extensions := [".png"]
  sniff := fun b => Id.run do
    if b.size < 8 then return false
    for i in [0:8] do
      if b.get! i != signature.get! i then return false
    return true
  decode := decode
  encode := encode

end PILean.Png
