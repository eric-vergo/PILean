/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Svg

/-!
# PDF objects as written

The objects of a PDF file as PILean writes them (ISO 32000-1, 7.3): `Pdf.Obj` and its text,
`Obj.write`, with names escaped (`#xx`) and strings written as hexadecimal strings, so that no
byte of a value can end the string or start another token; and the ten-digit offsets of a
cross-reference table.

## Main definitions

* `Pdf.Obj`, `Pdf.Obj.write`, `Pdf.nameText`, `Pdf.hexString`, `Pdf.pad10`.
-/

namespace PILean.Pdf

/-- A PDF object as the writer writes it. -/
inductive Obj where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- An integer. -/
  | int (n : Int)
  /-- A real number, written by `fmtNum` with `decimals` decimals. -/
  | real (x : Float) (decimals : Nat := 3)
  /-- A name, written `/name` (characters outside `!` to `~` and the delimiters as `#xx`). -/
  | name (s : String)
  /-- A string, written as a hexadecimal string `<…>` of its bytes. -/
  | str (b : ByteArray)
  /-- An array. -/
  | arr (xs : Array Obj)
  /-- A dictionary, its keys in order. -/
  | dict (kvs : Array (String × Obj))
  /-- A reference to the indirect object `n`, generation 0. -/
  | ref (n : Nat)
  deriving Inhabited

/-- Whether a byte is a PDF delimiter or white space (7.2.2), which a name must escape. -/
def special (b : UInt8) : Bool :=
  b ≤ 32 || b ≥ 127 || b == 35 || "()<>[]{}/%".toList.any (·.toNat == b.toNat)

/-- Two lowercase hexadecimal digits. -/
def hex2 (b : UInt8) : String :=
  let d := fun (k : Nat) => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

/-- A name's text after the slash: every special byte (`special`) as `#xx`. -/
def nameText (s : String) : String :=
  s.toUTF8.foldl (init := "") fun out b =>
    if special b then out ++ "#" ++ hex2 b else out.push (Char.ofNat b.toNat)

/-- The bytes as a hexadecimal string, `<…>`. -/
def hexString (b : ByteArray) : String :=
  b.foldl (init := "<") (fun out x => out ++ hex2 x) ++ ">"

/-- The object as PDF text, nested at most `fuel` deep (deeper parts are `null`). -/
def Obj.writeAt : Nat → Obj → String
  | 0, _ => "null"
  | _ + 1, .null => "null"
  | _ + 1, .bool b => if b then "true" else "false"
  | _ + 1, .int n => toString n
  | _ + 1, .real x k => fmtNum x k
  | _ + 1, .name s => "/" ++ nameText s
  | _ + 1, .str b => hexString b
  | fuel + 1, .arr xs => "[" ++ " ".intercalate (xs.toList.map (Obj.writeAt fuel)) ++ "]"
  | fuel + 1, .dict kvs =>
    "<<" ++ String.join (kvs.toList.map fun (k, v) => " /" ++ nameText k ++ " " ++ v.writeAt fuel) ++
      " >>"
  | _ + 1, .ref n => s!"{n} 0 R"

/-- The object as PDF text (at most 64 levels deep). -/
def Obj.write (o : Obj) : String := o.writeAt 64

/-- A number written with ten digits, zero-padded, as the cross-reference table writes offsets. -/
def pad10 (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (10 - s.length) '0') ++ s

end PILean.Pdf
