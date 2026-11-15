/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Verify

/-!
# `pilean-verify`

`lake exe pilean-verify DIR` checks the files of a directory written by `pilean-build` against its
`manifest.json` and the source record inside each file; see `PILean.Trust.Verify`.
-/

/-- Verifies the directory named by the one argument. -/
def main (args : List String) : IO UInt32 := PILean.Trust.verifyMain args
