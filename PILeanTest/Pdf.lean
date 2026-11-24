/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Examples
import PILeanTest.Diagrams
import PILeanTest.AlgebraDiagrams
import PILeanTest.NumberDiagrams

/-!
# PDF tests

The PDF writer on every picture of the gallery (plots, plane figures, diagrams, graphs, the
animations' posters, every frame of the gallery's explorer) and on samples that use every part of
it (gradients, clips, group opacity, dashes, the even-odd rule, a raster image with alpha): each
file passes the structural check (`Pdf.check`), is the same on a second run, and has a page of
`0.75` points per pixel of the picture. The check refuses planted faults, one per thing it checks.
The source record round-trips through the information dictionary (an incremental update), with
hostile values, and a second record is refused. Mutated and truncated files are read without a
crash by the source reader and the check (the bounded cases, with limits on memory and time, are
in `PILeanTest.Bounds`). A few PDFs of the gallery are goldens in `examples/`.

`lake exe pilean-test --pdf-out DIR` writes each gallery PDF with a PNG of the same picture
composited in sRGB (as a PDF viewer composites), for `tools/pdf-compare.py`.
-/

namespace PILeanTest.PdfChecks

open PILean PILean.Trust PILean.Canvas

/-- A drawing that uses every part of the writer: a linear and a radial gradient, a clip, a group
at an opacity, a dashed stroke with round caps and joins, a square cap, a bevel join, a path
filled by the even-odd rule, quadratic and cubic pieces, and a translucent fill. -/
def sampler : Shape :=
  let star := Path.polyline #[⟨60, 10⟩, ⟨90, 110⟩, ⟨10, 45⟩, ⟨110, 45⟩, ⟨30, 110⟩] |>.close
  let stops := #[(⟨0, ⟨230, 30, 30, 255⟩⟩ : Raster.Stop), ⟨1, ⟨20, 60, 220, 255⟩⟩]
  let curve := Path.empty.moveTo ⟨130, 100⟩ |>.quadTo ⟨170, 10⟩ ⟨210, 100⟩
    |>.cubicTo ⟨230, 140⟩ ⟨260, 20⟩ ⟨290, 100⟩
  .group #[
    .path (rect 0 0 320 200) (some (.solid ⟨250, 250, 245, 255⟩)),
    .path (rect 10 130 140 50) (some (.paint (.linear ⟨10, 0⟩ ⟨150, 0⟩ stops))),
    .path (circle ⟨240, 155⟩ 35) (some (.paint (.radial ⟨240, 155⟩ 35 stops))),
    .group #[.path star (some (.solid ⟨0, 114, 178, 255⟩))] (clip := some (rect 20 20 70 70)),
    .group #[.path (rect 120 20 60 60) (some (.solid ⟨213, 94, 0, 255⟩))
        (some { ink := ⟨0, 0, 0, 255⟩, width := 6 }),
      .path (circle ⟨180, 80⟩ 25) (some (.solid ⟨0, 158, 115, 255⟩))] (opacity := 0.5),
    .path curve none
      (some { ink := ⟨40, 40, 40, 255⟩, width := 4, cap := "round", join := "round",
              dash := #[12, 6] }),
    .path (Path.polyline #[⟨200, 20⟩, ⟨250, 60⟩, ⟨300, 20⟩]) none
      (some { ink := ⟨120, 0, 120, 255⟩, width := 8, cap := "square", join := "bevel" }),
    .path (rect 260 120 40 40) (some (.solid ⟨0, 0, 0, 255⟩)) (opacity := 0.3)]

/-- The sampler with its even-odd star: the SVG nodes with one path's rule changed. -/
def samplerNodes : Array Svg.Node :=
  let nodes := sampler.render (.native "sans-serif")
  nodes.push (Svg.el "path" #[("d", "M260 10 L300 10 L300 50 L260 50 Z M270 20 L290 20 L290 40 \
    L270 40 Z"), ("fill", "#cc79a7"), ("fill-rule", "evenodd")])

/-- The sampler as a PDF. -/
def samplerPdf : ByteArray := Pdf.ofSvgNodes 320 200 samplerNodes ⟨255, 255, 255, 255⟩

/-- An RGBA image of 40 × 30 pixels: a gradient of hues with alpha falling off to the right. -/
def rgbaImage : Image := Id.run do
  let mut im := Image.new .rgba 40 30 ⟨0, 0, 0, 0⟩
  for y in [0:30] do
    for x in [0:40] do
      im := im.putpixel x y ⟨(x * 6).toUInt8, (y * 8).toUInt8, 128, (255 - x * 6).toUInt8⟩
  return im

/-- The image as a PDF (empty if it cannot be written). -/
def imagePdf : ByteArray := (rgbaImage.toPdf).getD .empty

/-- Every picture of the gallery as a PDF, with its file stem and its size in pixels: the plots,
the plane figures and diagrams (light and dark, their narrow renditions too), the graphs, the
animations' posters and every frame of the explorer `windowRadius`, and the two samplers. -/
def galleryPdfs : Array (String × ByteArray × Float × Float) :=
  let stem := fun (n : String) => ((System.FilePath.mk n).fileStem.getD n)
  let plots := Examples.gallery.map fun (n, f) => (stem n, f.toPdf, f.width, f.height)
  let planes := (Examples.planes ++ Diagrams.gallery ++ AlgebraDiagrams.gallery ++
    NumberDiagrams.gallery).map fun (n, f) =>
      let g := f.autoPlaced
      (stem n, f.toPdf, g.frame.width.round, g.frame.height.round)
  let graphs := Examples.graphs.map fun (n, e, st) =>
    let l := e.layout st
    (n, l.toPdf st, l.width, l.height)
  let anims := Examples.animations.map fun (n, a) =>
    (n ++ "-poster", a.posterPdf, a.width.toFloat, a.height.toFloat)
  let x := Examples.PlaneFigures.windowRadius
  let frames := x.frames.zipIdx.map fun (f, k) =>
    (s!"window-radius-frame-{k}", f.toPdf, f.width, f.height)
  plots ++ planes ++ graphs ++ anims ++ frames ++
    #[("pdf-sampler", samplerPdf, 320, 200), ("pdf-image", imagePdf, 40, 30)]

/-- The page's `/MediaBox` of a file, as text of four numbers (`0 0 w h`), read with the bounded
reader. -/
def mediaBox? (d : ByteArray) : Option String := do
  let x ← (Pdf.readXref {} d).toOption
  let some (.ref root _) := x.trailer.get? "Root" | none
  let cat ← (Pdf.resolve {} d x (.ref root 0)).toOption
  let pages ← (Pdf.resolve {} d x (← cat.get? "Pages")).toOption
  let .arr kids ← pages.get? "Kids" | none
  let page ← (Pdf.resolve {} d x (← kids[0]?)).toOption
  let .arr box ← page.get? "MediaBox" | none
  some (" ".intercalate (box.toList.map fun
    | .int n => toString n
    | .real t => t
    | _ => "?"))

/-- The checks of every gallery PDF: the structural check passes with one page, the bytes are the
same when written again, and the page is `0.75` points per pixel. -/
def galleryChecks : Array (String × Bool) :=
  let again := galleryPdfs.map (·.2.1)
  galleryPdfs.zipIdx.flatMap fun ((name, pdf, w, h), k) =>
    let summary := Pdf.check pdf
    #[(s!"pdf {name}: passes the structural check with one page",
        match summary with | .ok s => s.pages == 1 && s.operators > 0 | .error _ => false),
      (s!"pdf {name}: deterministic", (again[k]?.map (·.data == pdf.data)).getD false),
      (s!"pdf {name}: the page is 0.75 pt per pixel",
        mediaBox? pdf == some s!"0 0 {fmtNum (w * 0.75)} {fmtNum (h * 0.75)}")]

/-- The messages of the check for each gallery PDF that fails it (empty when all pass). -/
def galleryProblems : Array String :=
  galleryPdfs.filterMap fun (name, pdf, _, _) =>
    match Pdf.check pdf with
    | .ok _ => none
    | .error e => some s!"{name}: {e}"

/-! ### Planted faults -/

/-- A small file written by hand from the writer's parts, uncompressed so that a fault can be
planted in its text: a page whose content draws a form (`/X0`) at an opacity (`/G0`), a shading
(`/S0`) inside a clip, and an image (`/X1`). `content` replaces the page's content and `extra`
the text of the resources' entries. -/
def handmade
    (content : String :=
      "q\n/G0 gs\n/X0 Do\nQ\nq\n0 0 10 10 re W n\n/S0 sh\nQ\nq\n4 0 0 4 0 0 cm\n/X1 Do\nQ\n")
    (resources : String := "<< /ExtGState << /G0 << /ca 0.5 /CA 0.5 >> >> /Shading << /S0 << \
      /ShadingType 2 /ColorSpace /DeviceRGB /Coords [0 0 10 0] /Function << /FunctionType 2 \
      /Domain [0 1] /C0 [1 0 0] /C1 [0 0 1] /N 1 >> /Extend [true true] >> >> /XObject << \
      /X0 6 0 R /X1 7 0 R >> >>")
    (form : String := "0 0 1 rg\n1 1 8 8 re\nf\n") (count : String := "1")
    (parent : String := "2 0 R")
    (image : ByteArray := ⟨#[255, 0, 0, 0, 255, 0, 0, 0, 255, 9, 9, 9]⟩)
    (lengthDelta : Int := 0) : ByteArray :=
  let catalog := "<< /Type /Catalog /Pages 2 0 R >>".toUTF8
  let pages := s!"<< /Type /Pages /Kids [3 0 R] /Count {count} >>".toUTF8
  let page := s!"<< /Type /Page /Parent {parent} /MediaBox [0 0 30 30] /Resources 4 0 R \
    /Contents 5 0 R >>".toUTF8
  let stream := fun (dict : String) (data : ByteArray) (delta : Int) =>
    s!"<< {dict} /Length {(data.size : Int) + delta} >>\nstream\n".toUTF8 ++ data ++
      "\nendstream".toUTF8
  let formObj := stream "/Type /XObject /Subtype /Form /BBox [0 0 10 10] /Resources 4 0 R"
    form.toUTF8 0
  let imageObj := stream "/Type /XObject /Subtype /Image /Width 2 /Height 2 /ColorSpace /DeviceRGB \
    /BitsPerComponent 8" image 0
  Pdf.document #[catalog, pages, page, resources.toUTF8, stream "" content.toUTF8 lengthDelta,
    formObj, imageObj] 1

/-- The bytes with the first occurrence of `a` replaced by `b` (unchanged when `a` is absent). -/
def replaceFirst (d : ByteArray) (a b : String) : ByteArray :=
  match findBytes d a.toUTF8 with
  | some i => d.extract 0 i ++ b.toUTF8 ++ d.extract (i + a.utf8ByteSize) d.size
  | none => d

/-- The faults the check must refuse, each with its name, on the hand-made file. -/
def faults : Array (String × ByteArray) :=
  let ok := handmade
  let off5 := match findBytes ok "\n5 0 obj".toUTF8 with | some i => i + 1 | none => 0
  #[("an offset in the table one byte off",
      replaceFirst ok s!"{Pdf.pad10 off5} 00000 n" s!"{Pdf.pad10 (off5 + 1)} 00000 n"),
    ("a stream's /Length one byte short", handmade (lengthDelta := -1)),
    ("a stream's /Length one byte long", handmade (lengthDelta := 1)),
    ("an object without endobj", replaceFirst ok "\nendobj\n4 0 obj" "\nendobx\n4 0 obj"),
    ("a reference to an object not in use", handmade (parent := "2 0 R /Annots [9 0 R]")),
    ("a /Count that is not the number of pages", handmade (count := "2")),
    ("a /Parent that is not the parent", handmade (parent := "1 0 R")),
    ("an unknown operator", handmade (content := "q\nzz\nQ\n")),
    ("Q without q", handmade (content := "Q\n")),
    ("q without Q", handmade (content := "q\n")),
    ("an operator with the wrong number of operands", handmade (content := "1 0 rg\n")),
    ("a gs name the resources lack", handmade (content := "/G9 gs\n")),
    ("an sh name the resources lack", handmade (content := "/S9 sh\n")),
    ("a Do name the resources lack", handmade (content := "/X9 Do\n")),
    ("an inline image", handmade (content := "BI /W 1 /H 1 ID x EI\n")),
    ("operands after the last operator", handmade (content := "1 2\n")),
    ("an image whose data is too short", handmade (image := ⟨#[1, 2, 3]⟩)),
    ("a form whose content is unbalanced", handmade (form := "q\n")),
    ("startxref pointing elsewhere", replaceFirst ok "startxref\n" "startxref\n1"),
    ("a file cut before its end", ok.extract 0 (ok.size - 30)),
    ("a file without its header", ok.extract 1 ok.size),
    ("a shading of an unknown type", replaceFirst ok "/ShadingType 2" "/ShadingType 7"),
    ("a key twice in a dictionary", replaceFirst ok "<< /Type /Catalog" "<< /Type /Catalog /Type"),
    ("a stream with damaged Flate data", replaceFirst ok "<< /Type /XObject /Subtype /Form"
        "<< /Filter /FlateDecode /Type /XObject /Subtype /Form")]

/-- The checks of the planted faults: the hand-made file passes, and each fault is refused. -/
def faultChecks : Array (String × Bool) :=
  #[("pdf check: the hand-made file passes",
      match Pdf.check handmade with
      | .ok s => s.pages == 1 && s.contents == 2
      | .error _ => false)] ++
    faults.map fun (name, d) =>
      (s!"pdf check: refuses {name}", match Pdf.check d with | .ok _ => false | .error _ => true)

/-! ### The source record -/

/-- A source with every field, its values hostile: non-ASCII letters, a character outside the
basic plane (a surrogate pair in UTF-16), parentheses and backslashes, a line feed, a tab. -/
def hostileSource : Source :=
  { module := "Ünïcode.Mod", decl := "Ünïcode.Mod.fig (𝔽) \\ ) (", file := "Ü/Mod.lean",
    line := 12, column := 3, repo := some "https://example.org/r?x=1&y=(2)",
    commit := some "0123abcd", version := "0.1.0", fingerprint := some (String.ofList
      (List.replicate 64 'a')), standing := some "linked", theorems := some "A.b C.d" }

/-- A plain source. -/
def plainSource : Source :=
  { module := "M", decl := "M.f", file := "M.lean", line := 1, column := 0, version := "0.1.0" }

/-- The checks of the source record in PDF files: written and read back on gallery files and the
samplers, the file still passing the structural check (the update chained through `/Prev`), the
pages unchanged, a second record refused, the dispatch by signature, an invalid source refused,
and a file with a damaged record refused by the reader. -/
def sourceChecks : Array (String × Bool) :=
  let pdfs := #[samplerPdf, imagePdf] ++ (galleryPdfs.extract 0 3).map (·.2.1)
  let roundTrips := pdfs.all fun d =>
    match withSourcePdf d hostileSource with
    | .ok e => (Source.read? e).toOption == some hostileSource && (Pdf.check e).isOk &&
        e.extract 0 d.size == d
    | .error _ => false
  let once := (withSourcePdf samplerPdf plainSource).toOption.getD .empty
  let damaged := replaceFirst once "/PILean:decl <" "/PILean:decl (x) /Junk <"
  #[("pdf source: hostile values round-trip, the file passes the check, its bytes kept",
      roundTrips),
    ("pdf source: a second record is refused", (withSourcePdf once plainSource).isOk == false),
    ("pdf source: withSource dispatches on %PDF-",
      ((withSource samplerPdf plainSource).toOption.bind fun e => (Source.read? e).toOption) ==
        some plainSource),
    ("pdf source: the format is detected as pdf", Source.format? samplerPdf == some "pdf"),
    ("pdf source: a file without a record has none", (Source.read? samplerPdf).isOk == false),
    ("pdf source: an invalid source is refused",
      (withSourcePdf samplerPdf { plainSource with module := "" }).isOk == false),
    ("pdf source: a record with a value that is not a text string is refused",
      (Source.read? damaged).isOk == false),
    ("pdf source: the information dictionary names the declaration",
      (findBytes once "/Title <feff004d002e0066>".toUTF8).isSome),
    ("pdf text strings: UTF-16 with a surrogate pair round-trips",
      Pdf.textString? (Pdf.utf16Text "a𝔽ü") == some "a𝔽ü"),
    ("pdf text strings: a lone surrogate is refused",
      Pdf.textString? ⟨#[0xFE, 0xFF, 0xD8, 0x00]⟩ == none)]

/-! ### Mutated files -/

/-- `n` copies of `d`, each with one byte changed or the file cut short, at positions and to
values from a fixed pseudo-random sequence. -/
def mutants (d : ByteArray) (n : Nat) : Array ByteArray := Id.run do
  let mut out := #[]
  let mut s : Nat := 2463534242
  for k in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let pos := (s >>> 20) % (max 1 d.size)
    let v := ((s >>> 12) % 256).toUInt8
    out := out.push (if k % 7 == 0 then d.extract 0 pos else d.set! pos v)
  return out

/-- The mutated files read by the source reader and the check: every one gives an answer (this
module runs in the test process, so a crash fails the run), and a mutant the check accepts is one
the source reader can read without failing for structural reasons. The number of mutants each
reader refused is returned with the check. -/
def mutationChecks : Array (String × Bool) × Nat × Nat :=
  let base := (withSourcePdf samplerPdf hostileSource).toOption.getD samplerPdf
  let ms := mutants base 600 ++ mutants imagePdf 200 ++ mutants handmade 300
  let refusedRead := ms.foldl (fun n m => if (Source.read? m).isOk then n else n + 1) 0
  let refusedCheck := ms.foldl (fun n m => if (Pdf.check m).isOk then n else n + 1) 0
  (#[("pdf mutants: 1100 mutated or cut files read without a crash", ms.size == 1100),
     ("pdf mutants: most are refused by the check", refusedCheck * 2 > ms.size)],
    refusedRead, refusedCheck)

/-- Dictionaries and arrays nest to the same depth, the reader's `maxDepth`: a value nested
`maxDepth - 1` deep is read, one nested `maxDepth` deep is refused, of either kind. -/
def nestingChecks : Array (String × Bool) :=
  let lim : Pdf.Limits := {}
  let arr := fun (k : Nat) => (String.ofList (List.replicate k '[') ++ "0" ++
    String.ofList (List.replicate k ']')).toUTF8
  let dict := fun (k : Nat) => (String.join (List.replicate k "<< /A ") ++ "0" ++
    String.join (List.replicate k " >>")).toUTF8
  let ok := fun (b : ByteArray) => (Pdf.parseValue lim b lim.maxDepth 0).isOk
  #[("pdf: arrays and dictionaries nest to the reader's depth and no further, alike",
      ok (arr (lim.maxDepth - 1)) && ok (dict (lim.maxDepth - 1)) &&
        !ok (arr lim.maxDepth) && !ok (dict lim.maxDepth))]

/-- All checks that need no files. -/
def checks : Array (String × Bool) :=
  galleryChecks ++ faultChecks ++ sourceChecks ++ mutationChecks.1 ++ nestingChecks

/-! ### Goldens and files for other software -/

/-- The gallery PDFs kept as goldens in `examples/`. -/
def goldens : Array String :=
  #["function-plot", "plane-constructions", "diagram-young", "graph-tree", "pdf-sampler"]

/-- Compares the golden PDFs with `examples/` (or rewrites them when `update`). -/
def goldenChecks (update : Bool) : IO (Array (String × Bool)) := do
  let mut r := #[]
  for g in goldens do
    let some (_, pdf, _, _) := galleryPdfs.find? (·.1 == g)
      | r := r.push (s!"pdf golden {g}", false)
    let path : System.FilePath := "examples" / s!"{g}.pdf"
    if update then
      IO.FS.writeBinFile path pdf
      IO.println s!"wrote {path}"
    else
      let old ← if ← path.pathExists then IO.FS.readBinFile path else pure .empty
      r := r.push (s!"pdf golden {path}: same", old.data == pdf.data)
  for p in galleryProblems do IO.eprintln s!"pdf: {p}"
  let (_, read, check) := mutationChecks
  IO.println s!"pdf mutants: the source reader refused {read} and the check {check} of 1100"
  return r

/-- Writes every gallery PDF with a PNG of the same picture composited in sRGB to `dir`
(`<stem>.pdf`, `<stem>.png`), for `tools/pdf-compare.py`. -/
def writeCompare (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let stem := fun (n : String) => ((System.FilePath.mk n).fileStem.getD n)
  let png := fun (w h : Float) (nodes : Array Svg.Node) (bg : Rgba) =>
    match (Raster.Svg.rasterize w.round.toUInt64.toNat h.round.toUInt64.toNat nodes bg
      (space := .srgb)).toImage.writePng with
    | .ok b => b
    | .error _ => ByteArray.empty
  let mut pngs : Array (String × ByteArray) := #[]
  for (n, f) in Examples.gallery do
    pngs := pngs.push (stem n, png f.width f.height (f.draw.render (.shapes f.style.text))
      f.style.background)
  for (n, f) in Examples.planes ++ Diagrams.gallery ++ AlgebraDiagrams.gallery ++
      NumberDiagrams.gallery do
    pngs := pngs.push (stem n, f.toPng.getD .empty)
  for (n, e, st) in Examples.graphs do
    let l := e.layout st
    pngs := pngs.push (n, png l.width l.height ((l.draw st).render (.shapes st.text)) st.background)
  for (n, a) in Examples.animations do
    pngs := pngs.push (n ++ "-poster", png a.width.toFloat a.height.toFloat
      ((a.frame a.poster).render (.shapes a.text)) a.background)
  for (f, k) in Examples.PlaneFigures.windowRadius.frames.zipIdx do
    pngs := pngs.push (s!"window-radius-frame-{k}", f.toPng.getD .empty)
  pngs := pngs.push ("pdf-sampler", png 320 200 samplerNodes ⟨255, 255, 255, 255⟩)
  for (n, pdf, _, _) in galleryPdfs do
    IO.FS.writeBinFile (dir / s!"{n}.pdf") pdf
    if let some (_, p) := pngs.find? (·.1 == n) then IO.FS.writeBinFile (dir / s!"{n}.png") p
  IO.println s!"wrote {galleryPdfs.size} PDFs to {dir}"

end PILeanTest.PdfChecks
