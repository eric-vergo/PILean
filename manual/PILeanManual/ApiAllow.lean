/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean

/-!
# The API reference's allow-list

The public declarations of the core that may appear in the API reference without a docstring,
each with the reason shown on its page. Two kinds are allowed:

* the declarations listed in `apiAllowList`, each with its reason (the list is empty);
* instances without a docstring whose last name component starts with `inst`, which is how Lean
  names an anonymous `instance` or one from a `deriving` clause (an instance given such a name
  by hand is allowed too): the class and the type in their signature say what they are.

Everything else must be documented: a public declaration that is neither fails the manual's build
(`PILeanManual.apiModule`) and `lake test`.
-/

namespace PILeanManual

open Lean

/-- The declarations allowed without a docstring, by name, with the reason. -/
def apiAllowList : Array (Name × String) := #[]

/-- The reason given for an instance whose last name component starts with `inst`, the form of
the names Lean gives an anonymous `instance` or one from a `deriving` clause. -/
def anonymousInstanceReason : String :=
  "an instance with a name of the form Lean gives an anonymous instance or one from a deriving \
  clause; its class and type, shown above, say what it is."

/-- Why `n` may lack a docstring, if it may: it is on `apiAllowList`, or it is an instance whose
last name component starts with `inst` (whether Lean or a person gave it that name). -/
def apiAllowed? (env : Environment) (n : Name) : Option String :=
  match apiAllowList.find? (·.1 == n) with
  | some (_, r) => some r
  | none =>
    let generated := match n with
      | .str _ s => s.startsWith "inst"
      | _ => false
    if Meta.isInstanceCore env n && generated then some anonymousInstanceReason else none

end PILeanManual
