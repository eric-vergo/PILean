import Tests.Framework
import Tests.Prng

/-!
# zlib tests

zlib (RFC 1950) framing: CMF/FLG header validation, FDICT rejection, and
Adler-32 trailer verification — all via hand-crafted malformed headers and
trailers that must be rejected with `.error`.
-/

namespace Tests.ZlibTests

open PILean
open PILean.Compress

/-- A known-good zlib stream (`Zlib.compress` of a small payload) to
mutate for the malformed-header/trailer cases below. -/
def goodPayload : ByteArray := "hello, zlib framing test".toUTF8

/-- A valid zlib stream wrapping `goodPayload`. -/
def goodStream : ByteArray := Zlib.compress goodPayload 6

/-- Assert `Zlib.decompress` rejects `v` with `.error`. -/
def assertZlibRejects (v : ByteArray) (label : String) : IO Unit := do
  match Zlib.decompress v with
  | .error _ => pure ()
  | .ok _ => fail s!"{label}: Zlib.decompress unexpectedly accepted malformed input"

/-- `goodStream` with byte `i` replaced by `b`. -/
def withByte (i : Nat) (b : UInt8) : ByteArray :=
  goodStream.set! i b

def suite : Tests.Suite :=
  { name := "zlib"
    cases := [
      test "a genuinely valid stream is accepted (sanity check for the mutations below)" do
        match Zlib.decompress goodStream with
        | .ok got => assertBytesEq got goodPayload "sanity"
        | .error e => fail s!"valid stream rejected: {e}",

      test "bad header check bits ((CMF*256+FLG) % 31 != 0) is rejected" do
        -- Flip a low bit of FLG (byte 1); at least one of the two choices
        -- breaks the mod-31 check bits (both can't stay valid, since valid
        -- streams have exactly one FLG per CMF satisfying it exactly).
        let mutated := withByte 1 ((goodStream.get! 1) ^^^ 0x01)
        assertZlibRejects mutated "bad check bits",

      test "unsupported compression method (CM ≠ 8) is rejected" do
        -- CMF's low nibble is CM; force it to 15 (keeping CINFO's high
        -- nibble), which is never method 8.
        let cmf := goodStream.get! 0
        let badCmf := (cmf &&& 0xF0) ||| 0x0F
        assertZlibRejects (withByte 0 badCmf) "bad CM",

      test "FDICT set is rejected (unsupported: no preset dictionary support)" do
        let flg := goodStream.get! 1
        assertZlibRejects (withByte 1 (flg ||| 0x20)) "FDICT set",

      test "corrupted Adler-32 trailer is rejected" do
        let n := goodStream.size
        let mutated := goodStream.set! (n - 1) ((goodStream.get! (n - 1)) ^^^ 0xFF)
        assertZlibRejects mutated "bad adler32",

      test "truncated trailer (missing Adler-32 bytes) is rejected" do
        assertZlibRejects (goodStream.extract 0 (goodStream.size - 2)) "truncated trailer",

      test "truncated header (fewer than 2 bytes) is rejected" do
        assertZlibRejects (ByteArray.mk #[0x78]) "truncated header",

      test "empty input is rejected" do
        assertZlibRejects ByteArray.empty "empty",

      test "truncated compressed body (header present, body cut) is rejected" do
        assertZlibRejects (goodStream.extract 0 3) "truncated body"
    ] }

end Tests.ZlibTests
