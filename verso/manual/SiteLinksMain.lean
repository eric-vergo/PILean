/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.SiteLinks

/-!
# `pilean-site-links`

Checks the links of a built site (`PILeanVerso.siteLinkProblems`):
`lake exe pilean-site-links SITE [--all]`, where `SITE` is the `html-multi` folder. It prints each
link that does not reach its target and exits with status 1 when there is one (or when no link
was checked), 0 otherwise. Without `--all` only PILean's links are checked.
-/

/-- Checks the site named by the arguments. -/
def main (args : List String) : IO UInt32 := do
  let (all, rest) := (args.contains "--all", args.filter (· != "--all"))
  let [site] := rest
    | IO.eprintln "usage: pilean-site-links SITE [--all]   (SITE: the html-multi folder)"; return 2
  unless ← System.FilePath.isDir site do
    IO.eprintln s!"pilean-site-links: no folder {site}"; return 2
  let (checked, problems) ← PILeanVerso.siteLinkProblems site all
  for p in problems do IO.println s!"dead link: {p}"
  IO.println s!"links: {checked} checked, {problems.size} dead"
  return if problems.isEmpty && checked > 0 then 0 else 1
