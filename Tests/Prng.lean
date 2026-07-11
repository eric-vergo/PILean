import PILean

/-!
# Deterministic PRNG for tests

SplitMix64 (Vigna's reference constants) — deterministic random bytes and
images for round-trip properties. Test data must be reproducible from a
seed; never use wall-clock or system randomness in tests.
-/

namespace Tests

open PILean

/-- SplitMix64 PRNG state. -/
structure SplitMix64 where
  state : UInt64
  deriving Repr, Inhabited

namespace SplitMix64

/-- Seed from a `Nat`. -/
def ofSeed (n : Nat) : SplitMix64 := ⟨UInt64.ofNat n⟩

/-- Next 64-bit output and advanced state (reference SplitMix64:
seed 0 first yields `0xE220A8397B1DCDAF`). -/
def next (g : SplitMix64) : UInt64 × SplitMix64 :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- `n` deterministic bytes. -/
def bytes (g : SplitMix64) (n : Nat) : ByteArray × SplitMix64 := Id.run do
  let mut g := g
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    let (v, g') := g.next
    g := g'
    out := out.push v.toUInt8
  return (out, g)

/-- A deterministic random image. `.palette`-mode images use the web-safe
palette with indices reduced into range. -/
def image (g : SplitMix64) (width height : Nat) (mode : Mode := .rgb) :
    Image × SplitMix64 := Id.run do
  let n := width * height * mode.bytesPerPixel
  let (raw, g') := g.bytes n
  let data := if mode == .palette then Id.run do
      let mut d := raw
      for i in [0:d.size] do
        d := d.set! i (d.get! i % 216)
      return d
    else raw
  let palette? := if mode == .palette then some Palette.webSafe else none
  return ({ width, height, mode, data, palette? }, g')

end SplitMix64

end Tests
