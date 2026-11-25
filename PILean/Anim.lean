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
import PILean.Anim.Animation
import PILean.Anim.Proofs
import PILean.Anim.Timeline
import PILean.Anim.TimelineProofs
import PILean.Anim.Smil

/-!
# Animated images

Frame sequences and the codecs for animated PNG and GIF: `FrameSeq.toApng`, `Anim.readApng`,
`FrameSeq.toGif`, `Anim.readGif`; animations (`Animation`); timelines of key-frame motions
(`Anim.Timeline`) and the SMIL animations that follow them (`Anim.Smil`). This module re-exports
its parts.
-/
