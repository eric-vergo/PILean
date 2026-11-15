/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Frames
import PILean.Anim.Compose
import PILean.Anim.Apng
import PILean.Anim.ApngRead
import PILean.Anim.Lzw
import PILean.Anim.Quantize
import PILean.Anim.Gif
import PILean.Anim.GifRead

/-!
# Animated images

Frame sequences and the codecs for animated PNG and GIF: `FrameSeq.toApng`, `Anim.readApng`,
`FrameSeq.toGif`, `Anim.readGif`. This module re-exports its parts.
-/
