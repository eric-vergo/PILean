/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# A small bounded JSON reader and writer

For the manifests of `pilean-build`: objects, arrays, strings, non-negative integers, booleans
and `null`. The reader treats its input as untrusted: the input is at most `maxJsonInput` bytes,
nesting is at most `maxJsonDepth`, an object has at most `maxJsonMembers` members and an array at
most `maxJsonItems` elements, strings are at most `maxJsonString` bytes, numbers have at most 15
digits and no fraction or exponent, and anything after the value is an error. All loops are
bounded by the input's length.
-/

namespace PILean.Trust

/-- The largest JSON input read, in bytes. -/
def maxJsonInput : Nat := 16 * 1024 * 1024

/-- The deepest nesting read. -/
def maxJsonDepth : Nat := 8

/-- The most elements of an array read. -/
def maxJsonItems : Nat := 100000

/-- The most members of an object read. -/
def maxJsonMembers : Nat := 64

/-- The longest string read, in bytes. -/
def maxJsonString : Nat := 65536

/-- A JSON value; numbers are non-negative integers. -/
inductive Json where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- A non-negative integer. -/
  | num (n : Nat)
  /-- A string. -/
  | str (s : String)
  /-- An array. -/
  | arr (xs : Array Json)
  /-- An object with its members in source order. -/
  | obj (kvs : Array (String × Json))
deriving Inhabited

namespace Json

/-- The string with the escapes of JSON: `"` and `\`, the control characters below 32 as `\n`,
`\r`, `\t` or `\u00XX`. Other characters are written as they are. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun out c =>
    if c == '"' then out ++ "\\\""
    else if c == '\\' then out ++ "\\\\"
    else if c == '\n' then out ++ "\\n"
    else if c == '\r' then out ++ "\\r"
    else if c == '\t' then out ++ "\\t"
    else if c.toNat < 32 then
      out ++ "\\u00" ++ String.ofList (Nat.toDigits 16 (c.toNat / 16)) ++
        String.ofList (Nat.toDigits 16 (c.toNat % 16))
    else out.push c

/-- The value of a member of an object, if the value is an object that has it (the first). -/
def get? : Json → String → Option Json
  | .obj kvs, k => (kvs.find? (·.1 == k)).map (·.2)
  | _, _ => none

/-- The reader's state: the input and the position. -/
structure Reader where
  /-- The input. -/
  d : ByteArray
  /-- The position of the next byte. -/
  pos : Nat

/-- Moves over white space (space, tab, line feed, carriage return). -/
def Reader.skipWs (r : Reader) : Reader := Id.run do
  let mut i := r.pos
  for _ in [0:r.d.size] do
    match r.d[i]? with
    | some b => if b == 32 || b == 9 || b == 10 || b == 13 then i := i + 1 else break
    | none => break
  return { r with pos := i }

/-- The value of a hexadecimal digit. -/
def hexVal? (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else none

/-- Reads a string whose opening quote is at the position; escapes `\" \\ \/ \b \f \n \r \t`
and `\uXXXX` (a surrogate pair is read as one character; a lone surrogate is an error). -/
def Reader.string (r : Reader) : Except String (String × Reader) := do
  if r.d[r.pos]? != some 34 then throw "a string was expected"
  let mut i := r.pos + 1
  let mut bytes := ByteArray.empty
  let mut closed := false
  for _ in [0:r.d.size] do
    let some b := r.d[i]? | throw "the string is not closed"
    if b == 34 then
      closed := true
      i := i + 1
      break
    else if b < 32 then throw "a control character in a string"
    else if b == 92 then
      let some e := r.d[i + 1]? | throw "the string is not closed"
      i := i + 2
      let simple : Option UInt8 :=
        if e == 34 then some 34 else if e == 92 then some 92 else if e == 47 then some 47
        else if e == 98 then some 8 else if e == 102 then some 12
        else if e == 110 then some 10 else if e == 114 then some 13
        else if e == 116 then some 9 else none
      if let some c := simple then bytes := bytes.push c
      else if e == 117 then
        let hex4 := fun (p : Nat) => do
          let mut v := 0
          for k in [0:4] do
            let some h := (r.d[p + k]?).bind hexVal? | throw "a bad \\u escape"
            v := v * 16 + h
          return v
        let v ← (hex4 i : Except String Nat)
        i := i + 4
        let cp ←
          if 0xD800 ≤ v && v < 0xDC00 then
            if r.d[i]? == some 92 && r.d[i + 1]? == some 117 then
              let w ← (hex4 (i + 2) : Except String Nat)
              if 0xDC00 ≤ w && w < 0xE000 then
                i := i + 6
                pure (0x10000 + (v - 0xD800) * 1024 + (w - 0xDC00))
              else throw "a lone surrogate"
            else throw "a lone surrogate"
          else if 0xDC00 ≤ v && v < 0xE000 then throw "a lone surrogate"
          else pure v
        if cp == 0 then throw "a NUL character"
        bytes := bytes ++ (String.singleton (Char.ofNat cp)).toUTF8
      else throw "a bad escape"
    else
      bytes := bytes.push b
      i := i + 1
    if bytes.size > maxJsonString then throw "a string is too long"
  if !closed then throw "the string is not closed"
  let some s := String.fromUTF8? bytes | throw "a string is not valid UTF-8"
  return (s, { r with pos := i })

/-- Reads a value of at most `depth` more levels of nesting. -/
def Reader.value : Nat → Reader → Except String (Json × Reader)
  | 0, _ => throw "nested too deeply"
  | depth + 1, r => do
    let r := r.skipWs
    let some b := r.d[r.pos]? | throw "unexpected end of input"
    let lit := fun (w : String) (v : Json) => do
      let bs := w.toUTF8
      if r.d.extract r.pos (r.pos + bs.size) == bs then
        return (v, { r with pos := r.pos + bs.size })
      else throw "unexpected character"
    if b == 34 then
      let (s, r) ← r.string
      return (.str s, r)
    else if b == 116 then lit "true" (.bool true)
    else if b == 102 then lit "false" (.bool false)
    else if b == 110 then lit "null" .null
    else if 48 ≤ b && b ≤ 57 then
      let mut i := r.pos
      let mut n := 0
      for _ in [0:16] do
        match r.d[i]? with
        | some c => if 48 ≤ c && c ≤ 57 then n := n * 10 + (c.toNat - 48); i := i + 1 else break
        | none => break
      if i - r.pos > 15 then throw "a number is too long"
      if r.d[r.pos]? == some 48 && i - r.pos > 1 then throw "a number with a leading zero"
      if let some c := r.d[i]? then
        if c == 46 || c == 101 || c == 69 then throw "only integers are read"
      return (.num n, { r with pos := i })
    else if b == 91 then
      let mut r : Reader := Reader.skipWs { r with pos := r.pos + 1 }
      let mut xs : Array Json := #[]
      if r.d[r.pos]? == some 93 then return (.arr xs, { r with pos := r.pos + 1 })
      for _ in [0:r.d.size] do
        let (v, r') ← Reader.value depth r
        xs := xs.push v
        if xs.size > maxJsonItems then throw "too many elements"
        r := r'.skipWs
        match r.d[r.pos]? with
        | some 44 => r := { r with pos := r.pos + 1 }
        | some 93 => return (.arr xs, { r with pos := r.pos + 1 })
        | _ => throw "a comma or a closing bracket was expected"
      throw "the array is not closed"
    else if b == 123 then
      let mut r : Reader := Reader.skipWs { r with pos := r.pos + 1 }
      let mut kvs : Array (String × Json) := #[]
      if r.d[r.pos]? == some 125 then return (.obj kvs, { r with pos := r.pos + 1 })
      for _ in [0:r.d.size] do
        let (k, r1) ← r.skipWs.string
        let r1 := r1.skipWs
        if r1.d[r1.pos]? != some 58 then throw "a colon was expected"
        let (v, r2) ← Reader.value depth { r1 with pos := r1.pos + 1 }
        if kvs.any (·.1 == k) then throw s!"the key {k} is repeated"
        kvs := kvs.push (k, v)
        if kvs.size > maxJsonMembers then throw "too many members"
        r := r2.skipWs
        match r.d[r.pos]? with
        | some 44 => r := { r with pos := r.pos + 1 }
        | some 125 => return (.obj kvs, { r with pos := r.pos + 1 })
        | _ => throw "a comma or a closing brace was expected"
      throw "the object is not closed"
    else throw "unexpected character"

/-- Reads a whole JSON text (see the module docstring for the limits); a failure is a message. -/
def parse (d : ByteArray) : Except String Json := do
  if d.size > maxJsonInput then throw "the input is too large"
  let (v, r) ← Reader.value maxJsonDepth { d, pos := 0 }
  let r := r.skipWs
  if r.pos != d.size then throw "something follows the value"
  return v

end Json

end PILean.Trust
