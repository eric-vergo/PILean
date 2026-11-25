/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Trust

/-!
# Inert SVG tests

`Svg.isInert` accepts every SVG file of the gallery, a figure with a source record, and small
hand-written documents; it refuses documents with script, outside references, event handlers,
animations started or ended by events, declarations, escapes in style text, unbalanced or too deep
nesting, and inputs above the size cap.
-/

namespace PILeanTest.Inert

open PILean PILean.Svg

/-- A document with `body` inside the root element. -/
def doc (body : String) : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\">" ++ body ++ "</svg>"

/-- Whether the document is accepted. -/
def ok (s : String) : Bool := isInert s

/-- Whether the document is refused. -/
def bad (s : String) : Bool := !isInert s

/-- `2 ^ k` bytes of `a`, built by doubling. -/
def big (k : Nat) : String := Id.run do
  let mut s := "a"
  for _ in [0:k] do s := s ++ s
  return s

/-- `n` nested `g` elements inside a root. -/
def nested (n : Nat) : String :=
  doc ("".intercalate (List.replicate n "<g>") ++ "".intercalate (List.replicate n "</g>"))

/-- The checks that need no files. -/
def checks : Array (String × Bool) :=
  let withSource := PILeanTest.Trust.okOr (PILean.Trust.withSourceSvg PILeanTest.Trust.figure.toSvg
    PILeanTest.Trust.sample) ""
  #[("inert: a figure with a source record", ok withSource && withSource.length > 0),
    ("inert: the minimal document", ok "<svg xmlns=\"http://www.w3.org/2000/svg\"/>"),
    ("inert: the declaration, comments and white space around the root",
      ok ("<?xml version=\"1.0\"?>\n<!-- a -->\n" ++ doc "<!-- b --><g/>" ++ "\n<!-- c -->\n")),
    ("inert: a link to a fragment", ok (doc "<g href=\"#a\"/><g xlink:href=\"#a\"/>")),
    ("inert: a url to a fragment",
      ok (doc "<g clip-path=\"url(#c)\" fill=\"url( '#c')\"/>")),
    ("inert: single quotes and entities in values",
      ok (doc "<text font-family='a &amp; b' x=\"&#49;\">&lt;&foo;</text>")),
    ("inert: a style element of the writer",
      ok (doc ("<style>.a{display:none}@media (prefers-reduced-motion: reduce)" ++
        "{.a{fill:red}}</style>"))),
    ("inert: an animation of an ordinary attribute",
      ok (doc "<rect><animate attributeName=\"opacity\" values=\"0;1\" dur=\"1s\"/></rect>")),
    ("inert: nesting 256 deep is accepted", ok (nested 255)),
    ("inert: the empty document is refused", bad ""),
    ("inert: a script element is refused", bad (doc "<script>alert(1)</script>")),
    ("inert: a script element in capitals is refused", bad (doc "<SCRIPT>alert(1)</SCRIPT>")),
    ("inert: foreignObject is refused", bad (doc "<foreignObject/>")),
    ("inert: image is refused", bad (doc "<image href=\"x.png\"/>")),
    ("inert: use of an outside document is refused",
      bad (doc "<use href=\"http://e/x#a\"/>")),
    ("inert: use is refused even for a fragment", bad (doc "<use href=\"#a\"/>")),
    ("inert: a javascript link is refused",
      bad (doc "<a href=\"javascript:alert(1)\"><text>x</text></a>")),
    ("inert: onload is refused", bad "<svg xmlns=\"http://www.w3.org/2000/svg\" onload=\"f()\"/>"),
    ("inert: ONLOAD is refused", bad "<svg xmlns=\"http://www.w3.org/2000/svg\" ONLOAD=\"f()\"/>"),
    ("inert: onclick on an inner element is refused", bad (doc "<g><rect onclick=\"f()\"/></g>")),
    ("inert: a data link is refused", bad (doc "<g xlink:href=\"data:text/html,x\"/>")),
    ("inert: an href that is not a fragment is refused", bad (doc "<g href=\"x.svg\"/>")),
    ("inert: an entity-hidden javascript link is refused",
      bad (doc "<g href=\"&#106;avascript:x\"/>")),
    ("inert: a hexadecimal-entity-hidden javascript link is refused",
      bad (doc "<g fill=\"&#x6A;avascript:x\"/>")),
    ("inert: javascript with white space inside is refused",
      bad (doc "<g fill=\"java&#9;script:x\"/>")),
    ("inert: a url to another document is refused", bad (doc "<g fill=\"url(http://e/x)\"/>")),
    ("inert: a quoted url to another document is refused",
      bad (doc "<g fill=\"url( 'x')\"/>")),
    ("inert: a style attribute is refused", bad (doc "<g style=\"background:url(x)\"/>")),
    ("inert: xml:base is refused", bad (doc "<g xml:base=\"http://e/\"/>")),
    ("inert: a style import is refused", bad (doc "<style>@import url(x)</style>")),
    ("inert: a style url with spaces and quotes is refused",
      bad (doc "<style>a{b:url( 'x' )}</style>")),
    ("inert: a backslash in style is refused", bad (doc "<style>a{b:\\75rl(x)}</style>")),
    ("inert: a character reference in style is refused",
      bad (doc "<style>a{b:&#117;rl(x)}</style>")),
    ("inert: markup in style is refused", bad (doc "<style><g/></style>")),
    ("inert: an unterminated style is refused", bad (doc "<style>a{}")),
    ("inert: a document type is refused",
      bad ("<!DOCTYPE svg>" ++ doc "")),
    ("inert: an entity declaration is refused",
      bad ("<!DOCTYPE svg [<!ENTITY a \"b\">]>" ++ doc "")),
    ("inert: an entity declaration inside is refused", bad (doc "<!ENTITY a \"b\">")),
    ("inert: a CDATA section is refused", bad (doc "<![CDATA[x]]>")),
    ("inert: another processing instruction is refused",
      bad ("<?xml-stylesheet href=\"a.css\"?>" ++ doc "")),
    ("inert: a declaration after the start is refused",
      bad (doc "" ++ "<?xml version=\"1.0\"?>")),
    ("inert: setting href is refused",
      bad (doc "<set attributeName=\"href\" to=\"javascript:x\"/>")),
    ("inert: setting xlink:href is refused",
      bad (doc "<set attributeName=\"xlink:href\" to=\"#a\"/>")),
    ("inert: animating an event handler is refused",
      bad (doc "<animate attributeName=\"onclick\" values=\"a;b\" dur=\"1s\"/>")),
    ("inert: attributeName in another letter case is still checked",
      bad (doc "<set attributename=\"onclick\" to=\"f()\"/>") &&
        bad (doc "<set ATTRIBUTENAME=\"href\" to=\"#a\"/>")),
    ("inert: an image function in an attribute value is refused",
      bad (doc "<g cursor=\"image-set(&quot;http://e/x.png&quot; 1x),auto\"/>") &&
        bad (doc "<g fill=\"image(&quot;http://e/x.png&quot;)\"/>") &&
        bad (doc "<set attributeName=\"cursor\" to=\"cross-fade(a, b)\"/>") &&
        bad (doc "<g fill=\"src(&quot;http://e/x&quot;)\"/>")),
    ("inert: animations on the clock are accepted",
      ok (doc ("<g><animate attributeName=\"opacity\" values=\"0;1\" dur=\"1s\" begin=\"0s\" " ++
        "end=\"indefinite\"/><set attributeName=\"opacity\" to=\"0\" begin=\"-1.5s; 2min\" " ++
        "end=\"01:02.5\"/><animateTransform attributeName=\"transform\" type=\"rotate\" " ++
        "values=\"0;90\" dur=\"2s\" begin=\"+300ms;5\" end=\"1h\"/></g>"))),
    ("inert: an animation that an event starts or ends is refused",
      bad (doc "<animate attributeName=\"opacity\" values=\"0;1\" dur=\"1s\" begin=\"click\"/>") &&
        bad (doc "<set attributeName=\"opacity\" to=\"0\" begin=\"foo.mouseover\"/>") &&
        bad (doc "<set attributeName=\"opacity\" to=\"0\" end=\"accessKey(a)\"/>") &&
        bad (doc ("<animate attributeName=\"opacity\" values=\"0;1\" dur=\"1s\" " ++
          "begin=\"0s;click\"/>")) &&
        bad (doc ("<animateTransform attributeName=\"transform\" type=\"rotate\" " ++
          "values=\"0;90\" dur=\"1s\" end=\"focusin\"/>"))),
    ("inert: an animation tied to another element's timing or the wall clock is refused",
      bad (doc "<set attributeName=\"opacity\" to=\"0\" begin=\"a.end+1s\"/>") &&
        bad (doc "<set attributeName=\"opacity\" to=\"0\" begin=\"a.repeat(2)\"/>") &&
        bad (doc ("<set attributeName=\"opacity\" to=\"0\" " ++
          "begin=\"wallclock(2026-01-01T00:00)\"/>")) &&
        bad (doc "<set attributeName=\"opacity\" to=\"0\" begin=\"1s.click\"/>") &&
        bad (doc "<set attributeName=\"opacity\" to=\"0\" begin=\"\"/>")),
    ("inert: begin and end are checked in any letter case and through references",
      bad (doc "<set attributeName=\"opacity\" to=\"0\" BEGIN=\"click\"/>") &&
        bad (doc "<set attributeName=\"opacity\" to=\"0\" End=\"&#99;lick\"/>") &&
        inertProblem? (doc "<set attributeName=\"opacity\" to=\"0\" begin=\"click\"/>") ==
          some "the event-based timing begin=\"click\""),
    ("inert: an unknown entity is refused", bad (doc "<g fill=\"&foo;\"/>")),
    ("inert: an entity without a semicolon is refused", bad (doc "<g fill=\"a & b\"/>")),
    ("inert: a reference to NUL is refused", bad (doc "<g fill=\"&#0;\"/>")),
    ("inert: an unclosed element is refused", bad "<svg xmlns=\"http://www.w3.org/2000/svg\"><g>"),
    ("inert: an unterminated tag is refused", bad "<svg xmlns=\"http://www.w3.org/2000/svg\""),
    ("inert: mismatched nesting is refused", bad (doc "<g><rect></g></rect>")),
    ("inert: a stray end tag is refused", bad (doc "</g>")),
    ("inert: two root elements are refused", bad (doc "" ++ doc "")),
    ("inert: text after the root is refused", bad (doc "" ++ "x")),
    ("inert: text before the root is refused", bad ("x" ++ doc "")),
    ("inert: a root that is not svg is refused", bad "<g/>"),
    ("inert: an unknown element is refused", bad (doc "<blink/>")),
    ("inert: nesting deeper than 256 is refused", bad (nested 300)),
    ("inert: an unterminated comment is refused", bad (doc "<!-- x")),
    ("inert: a comment an HTML parser would end at once is refused",
      bad (doc "<!--><script>alert(1)</script>-->") &&
        bad (doc "<!---><script>alert(1)</script>-->")),
    ("inert: a comment with -- inside, which an HTML parser may end early, is refused",
      bad (doc "<!-- a --!><script>alert(1)</script> -->") && bad (doc "<!-- a -- b -->") &&
        bad (doc "<!-- a --->")),
    ("inert: a declaration with a > or a < inside is refused",
      bad ("<?xml version=\"1.0\" a=\">\"<script>alert(1)</script> ?>" ++ doc "") &&
        bad ("<?xml version=\"1.0\" a=\"<\"?>" ++ doc "")),
    ("inert: an attribute without quotes is refused", bad (doc "<g fill=red/>")),
    ("inert: an attribute without a value is refused", bad (doc "<g fill/>")),
    ("inert: an unterminated value is refused", bad (doc "<g fill=\"red/>")),
    ("inert: attributes without a space between are refused",
      bad (doc "<g fill=\"red\"stroke=\"b\"/>")),
    ("inert: an attribute name with other characters is refused", bad (doc "<g f$ll=\"red\"/>")),
    ("inert: a raw < in a value is refused", bad (doc "<g fill=\"a<b\"/>")),
    ("inert: above the size cap is refused without scanning",
      inertProblem? (big 26 ++ "a") == some "the document is larger than 64 MiB"),
    ("inert: a large comment is scanned", ok (doc ("<!--" ++ big 20 ++ "-->"))),
    ("inert: the problem names the reason",
      inertProblem? (doc "<script/>") == some "the element <script>" &&
        (inertProblem? (doc "")).isNone)]

/-- Every `examples/*.svg` file is accepted. -/
def ioChecks : IO (Array (String × Bool)) := do
  let mut out := #[]
  let mut n := 0
  for e in (← System.FilePath.readDir "examples") do
    if e.path.extension == some "svg" then
      let s ← IO.FS.readFile e.path
      n := n + 1
      out := out.push (s!"inert: examples/{e.fileName} is accepted", isInert s)
  out := out.push ("inert: the gallery has SVG files", n > 0)
  return out

end PILeanTest.Inert
