import PILean
import GalleryLib.Mobius.Exact

/-!
# Möbius flow — the Float render layer

Skeleton — the render work package implements: Float complex mini-ops,
HSV domain coloring of `f(w) = (w³−1)/(w³+1)`, the Möbius map from
`entries ∘ normalize` (ℚ → Float conversion once per frame:
`(Float.ofInt q.num) / (Float.ofNat q.den)`), the swirl frame family, and
the composition finale with its runtime byte-equality witness.
-/

namespace Gallery.Mobius

end Gallery.Mobius
