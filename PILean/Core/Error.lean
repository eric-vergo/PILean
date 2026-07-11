import PILean.Core.Mode

/-!
# Error types

Errors for the pure encode/decode layer. Project law: codec code returns
these via `Except` and never panics on input data, no matter how malformed;
`panic!` anywhere in PILean means "bug in PILean", never "bad user input".
The `IO` boundary (`Image.load`/`Image.save`) renders them into
`IO.userError`.
-/

namespace PILean

/-- Why a byte stream could not be decoded into an image. -/
inductive DecodeError where
  /-- The input ended before the structure at `offset` was complete. -/
  | truncated (offset : Nat) (what : String)
  /-- The input does not start with `format`'s magic bytes. -/
  | badMagic (format : String)
  /-- Structurally invalid data at (or near) byte `offset`. -/
  | corrupt (offset : Nat) (msg : String)
  /-- Valid data using a `format` feature PILean does not (yet) support. -/
  | unsupported (format : String) (feature : String)
  /-- No codec recognized the input. -/
  | unknownFormat
  deriving Repr, Inhabited

/-- Human-readable rendering. -/
def DecodeError.render : DecodeError → String
  | .truncated off what => s!"truncated input at byte {off}: {what}"
  | .badMagic fmt => s!"not a {fmt} file (bad magic bytes)"
  | .corrupt off msg => s!"corrupt data at byte {off}: {msg}"
  | .unsupported fmt feat => s!"unsupported {fmt} feature: {feat}"
  | .unknownFormat => "unrecognized image format"

instance : ToString DecodeError := ⟨DecodeError.render⟩

/-- Why an image could not be encoded. -/
inductive EncodeError where
  /-- `format` cannot represent images in `mode` (convert first). -/
  | unsupportedMode (format : String) (mode : Mode)
  /-- An encode option or input was invalid. -/
  | invalidArg (msg : String)
  deriving Repr, Inhabited

/-- Human-readable rendering. -/
def EncodeError.render : EncodeError → String
  | .unsupportedMode fmt m => s!"cannot encode mode {m} as {fmt}"
  | .invalidArg msg => s!"invalid argument: {msg}"

instance : ToString EncodeError := ⟨EncodeError.render⟩

end PILean
