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
* instances whose names Lean made up (`inst…`), from an anonymous `instance` or a `deriving`
  clause, when they have no docstring: the class and the type in their signature say what they
  are.

Everything else must be documented: a public declaration that is neither fails the manual's build
(`PILeanManual.apiModule`) and `lake test`.
-/

namespace PILeanManual

open Lean

/-- The declarations allowed without a docstring, by name, with the reason. -/
def apiAllowList : Array (Name × String) := #[]

/-- The reason given for an instance whose name Lean made up (`inst…`, from an anonymous
`instance` or a `deriving` clause). -/
def anonymousInstanceReason : String :=
  "an instance whose name Lean made up (an anonymous instance or one from a deriving clause); \
  its class and type, shown above, say what it is."

/-- Why `n` may lack a docstring, if it may: it is on `apiAllowList`, or it is an instance whose
name Lean made up (its last component starts with `inst`). -/
def apiAllowed? (env : Environment) (n : Name) : Option String :=
  match apiAllowList.find? (·.1 == n) with
  | some (_, r) => some r
  | none =>
    let generated := match n with
      | .str _ s => s.startsWith "inst"
      | _ => false
    if Meta.isInstanceCore env n && generated then some anonymousInstanceReason else none

end PILeanManual
