/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Checking the links of a built site

`siteLinkProblems` reads the pages of a site that Verso wrote (the `html-multi` folder) and
reports every link into the site that does not reach its target: the file it names must exist (a
folder stands for its `index.html`), and its fragment, when it has one, must be the `id` of an
element of that page. Links are resolved as a browser resolves them: against the page's address
and its `<base>`, with percent escapes and character references decoded.

By default only PILean's links are checked: those of an `a` element with a class that starts with
`pilean-` (the figures, the figures page and the figures' pages mark every link they write that
way). With `all := true`, every link of the site is held to the same rule. Links with a scheme
(`https:`, `lean:`, …) and links to another host are not checked, nor is a bare fragment that
names an element a page's script makes (`scriptPlaces`: the Verso Blueprint motion switch,
`#bp-motion`, which a motion's caption links).

The pages are read as Verso writes them: attribute values in double quotes, `<`, `>`, `&` and
`"` in them written as character references, and no tag inside `script` and `style` elements.
-/

namespace PILeanVerso

/-- The characters of a tag or attribute name. -/
private def nameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == ':' || c == '_'

/-- `s` with the character references `&amp;`, `&lt;`, `&gt;`, `&quot;`, `&#39;` and `&#x27;`
replaced by their characters. -/
def unescapeHtml (s : String) : String :=
  let s := (s.replace "&lt;" "<").replace "&gt;" ">"
  let s := ((s.replace "&quot;" "\"").replace "&#39;" "'").replace "&#x27;" "'"
  s.replace "&amp;" "&"

/-- The value of a hexadecimal digit. -/
private def hexValue? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `s` with its percent escapes decoded as UTF-8; an escape that is not one, or bytes that are
not UTF-8, are kept as written. -/
def percentDecode (s : String) : String := Id.run do
  let mut out := ByteArray.empty
  let mut cs := s.toList
  while !cs.isEmpty do
    match cs with
    | '%' :: a :: b :: rest =>
      match hexValue? a, hexValue? b with
      | some x, some y =>
        out := out.push (x * 16 + y).toUInt8
        cs := rest
      | _, _ =>
        out := out ++ "%".toUTF8
        cs := a :: b :: rest
    | c :: rest =>
      out := out ++ (String.singleton c).toUTF8
      cs := rest
    | [] => pure ()
  return (String.fromUTF8? out).getD s

/-- The attributes of an opening tag, from the text after its name up to its `>`: each name with
its value, character references decoded (`""` for an attribute without a value). -/
def tagAttrs (text : String) : Array (String × String) := Id.run do
  let mut out := #[]
  let mut cs := text.toList
  while !cs.isEmpty do
    cs := cs.dropWhile fun c => c.isWhitespace || c == '/'
    let name := cs.takeWhile fun c => !(c.isWhitespace || c == '=' || c == '/')
    if name.isEmpty then
      cs := cs.drop 1
      continue
    cs := cs.drop name.length
    match cs with
    | '=' :: '"' :: rest =>
      let v := rest.takeWhile (· != '"')
      out := out.push (String.ofList name |>.toLower, unescapeHtml (String.ofList v))
      cs := rest.drop (v.length + 1)
    | _ => out := out.push (String.ofList name |>.toLower, "")
  return out

/-- What the check needs of a page: the ids of its elements, its `<base>`, and its links (the
`href` and the class of each `a` element). -/
structure PageLinks where
  /-- The ids of the page's elements. -/
  ids : Std.HashSet String := {}
  /-- The address of the page's first `<base>`. -/
  base : Option String := none
  /-- Each link's `href` and `class`. -/
  links : Array (String × String) := #[]

/-- Reads a page: every opening tag outside `script` and `style` elements, with its
attributes. -/
def PageLinks.read (html : String) : PageLinks := Id.run do
  let mut p : PageLinks := {}
  let mut skip : Option String := none
  for piece in (html.splitOn "<").drop 1 do
    if let some t := skip then
      if piece.startsWith s!"/{t}" then skip := none
      continue
    let cs := piece.toList
    let tag := String.ofList (cs.takeWhile nameChar) |>.toLower
    if tag.isEmpty then continue
    let rest := String.ofList ((cs.drop tag.length).takeWhile (· != '>'))
    let attrs := tagAttrs rest
    let get := fun (k : String) => (attrs.find? (·.1 == k)).map (·.2)
    if let some i := get "id" then p := { p with ids := p.ids.insert i }
    if tag == "base" && p.base.isNone then p := { p with base := get "href" }
    if tag == "a" || tag == "area" then
      if let some h := (get "href").orElse fun _ => get "xlink:href" then
        p := { p with links := p.links.push (h, (get "class").getD "") }
    if tag == "script" || tag == "style" then skip := some tag
  return p

/-- Whether `href` names a scheme (`https:`, `lean:`, `mailto:`) or another host (`//`). -/
def leavesSite (href : String) : Bool :=
  let schemeChar := fun c => c.isAlphanum || c == '+' || c == '-' || c == '.'
  href.startsWith "//" ||
    match href.toList with
    | c :: rest => c.isAlpha && (rest.dropWhile schemeChar).head? == some ':'
    | [] => false

/-- The ids of elements that a page's script makes rather than its markup, which a link may name
as a bare fragment: the Verso Blueprint motion switch (`bp-motion`), whose script also follows
such a link itself and whose stylesheet shows the link only when scripts run. -/
def scriptPlaces : List String := ["bp-motion"]

/-- The folders and file that the relative address `ref` names from the folder `dir` (both lists
of components from the site's root); `none` when it goes above the root. The `Bool` says that the
address names a folder (it ends in `/`, `.` or `..`, or is empty). -/
def resolvePath (dir : List String) (ref : String) : Option (List String × Bool) := do
  let comps := ref.splitOn "/"
  let start := if ref.startsWith "/" then [] else dir
  let mut out := start.reverse
  for c in comps do
    if c.isEmpty || c == "." then continue
    if c == ".." then
      match out with
      | _ :: rest => out := rest
      | [] => failure
    else out := percentDecode c :: out
  let last := comps.getLast?.getD ""
  pure (out.reverse, last.isEmpty || last == "." || last == "..")

/-- The problems of one link: `none` when it reaches its target. `pages` reads a page of the site
by its path from the root. -/
def linkProblem? (root : System.FilePath) (dir : List String) (base : Option String)
    (href : String) (pages : List String → IO (Option PageLinks)) : IO (Option String) := do
  let (pathPart, frag) := match href.splitOn "#" with
    | p :: f :: more => (p, some ("#".intercalate (f :: more)))
    | _ => (href, none)
  let pathPart := (pathPart.splitOn "?").headD ""
  -- the folder links resolve from: the page's, or its `<base>`'s
  let baseDir ← match base with
    | none => pure (some dir)
    | some b => pure <| (resolvePath dir b).map fun (cs, isDir) => if isDir then cs else cs.dropLast
  let some baseDir := baseDir | return some "its page's <base> goes above the site's root"
  let some (comps, isDir) := resolvePath baseDir pathPart
    | return some "it goes above the site's root"
  let file := comps.foldl (· / ·) root
  let (comps, file) ← if isDir || (← file.isDir) then
      pure (comps ++ ["index.html"], file / "index.html")
    else pure (comps, file)
  unless ← file.pathExists do
    return some s!"no file {"/".intercalate comps}"
  let some f := frag | return none
  let f := percentDecode f
  if f.isEmpty then return none
  unless file.toString.endsWith ".html" do
    return some s!"the fragment #{f} names an element of {"/".intercalate comps}, not a page"
  let some p ← pages comps | return some s!"{"/".intercalate comps} cannot be read"
  if p.ids.contains f then return none
  return some s!"{"/".intercalate comps} has no element with the id {f}"

/-- The pages below `dir`, as paths of components from it. -/
private partial def htmlFiles (dir : System.FilePath) (rel : List String := []) :
    IO (Array (List String)) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← htmlFiles e.path (rel ++ [e.fileName]))
    else if e.fileName.endsWith ".html" then out := out.push (rel ++ [e.fileName])
  return out

/-- Whether a link with the class attribute `cls` is PILean's: one of its classes starts with
`pilean-`. -/
def pileanLink (cls : String) : Bool :=
  (cls.split Char.isWhitespace).toList.any fun c => c.toString.startsWith "pilean-"

/-- Checks the links of the site in `root` (the `html-multi` folder): the number of links checked
and a line for each that does not reach its target, naming the page, the link and why. Only
PILean's links (`pileanLink`) are checked unless `all` is set. -/
def siteLinkProblems (root : System.FilePath) (all : Bool := false) :
    IO (Nat × Array String) := do
  let files := (← htmlFiles root).qsort fun a b => "/".intercalate a < "/".intercalate b
  let cache ← IO.mkRef (∅ : Std.HashMap (List String) PageLinks)
  let pages : List String → IO (Option PageLinks) := fun comps => do
    if let some p := (← cache.get)[comps]? then return some p
    let path := comps.foldl (· / ·) root
    try
      let p := PageLinks.read (← IO.FS.readFile path)
      cache.modify (·.insert comps p)
      return some p
    catch _ => return none
  let mut checked := 0
  let mut out := #[]
  for comps in files do
    let some p ← pages comps | out := out.push s!"{"/".intercalate comps}: cannot be read"
    for (href, cls) in p.links do
      if !(all || pileanLink cls) || leavesSite href then continue
      if scriptPlaces.any (href == "#" ++ ·) then continue
      checked := checked + 1
      if let some why ← linkProblem? root comps.dropLast p.base href pages then
        out := out.push s!"{"/".intercalate comps}: {href} ({cls}): {why}"
  return (checked, out)

end PILeanVerso
