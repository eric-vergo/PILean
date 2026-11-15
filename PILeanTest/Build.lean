/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples
import PILean.Trust.Build

/-!
# `pilean-build` for the gallery

`lake exe pilean-build [--out DIR] [--repo URL] [--commit SHA] [--check]` renders the gallery
figures that have the attribute `figure` (see `PILean.Trust.Attr`) into a directory and writes
the manifest, or checks a directory against what the build produces. Exit status 0, 1 if a file
is stale, missing or extra or a figure cannot be rendered, 2 on a wrong command line.
-/

/-- The driver: the tagged figures of the library's gallery. -/
def main (args : List String) : IO UInt32 := PILean.Trust.buildMain figures% args
