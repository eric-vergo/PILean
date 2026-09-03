import PILean.Core.Mode
import PILean.Core.Color
import PILean.Core.Geometry
import PILean.Core.Error
import PILean.Core.Palette
import PILean.Core.Image
import PILean.Core.Convert
import PILean.Core.Paste
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Compress.Checksum
import PILean.Compress.BitStream
import PILean.Compress.Huffman
import PILean.Compress.LZ77
import PILean.Compress.Inflate
import PILean.Compress.Deflate
import PILean.Compress.Zlib
import PILean.Compress.Lzw
import PILean.Codec.Types
import PILean.Codec.Netpbm
import PILean.Codec.Bmp
import PILean.Codec.Qoi
import PILean.Codec.Png
import PILean.Codec.Gif
import PILean.Codec.Jpeg
import PILean.Codec.Tiff
import PILean.Color.Quantize
import PILean.Draw.Basic
import PILean.Draw.Path
import PILean.Draw.Text
import PILean.Font.Bitmap
import PILean.Transform.Basic
import PILean.Transform.Resize
import PILean.Filter.Point
import PILean.Filter.Kernel
import PILean.IO

/-!
# PILean

A pure Lean 4 imaging library — a functional port of Python's PIL/Pillow.
Create images, draw on them, transform them, and read/write standard file
formats, with zero dependencies.

```lean
open PILean

def main : IO Unit := do
  let img := Image.new 320 240 |>.putPixel 10 10 Color.red
  let img := Draw.line img ⟨0, 0⟩ ⟨319, 239⟩ (Color.rgb 0 255 0)
  img.save "out.png"
```
-/
