/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Import graphs used to measure the layered layout

Two real dependency graphs as edge lists of module names: the imports between the modules of this
library (taken from its sources), and those of a project of about a hundred modules (names
replaced by neutral ids); and two dependency graphs of blueprints with their chapters and sections
(names removed, label lengths kept). They are fixtures for `PILeanTest.Graphs` (`--graph-bench`,
`--graph-compare-out`).
-/

namespace PILeanTest.Fixtures

/-- The import edges of a 100-module project (89 modules, 173 internal imports; names replaced
by neutral ids): `(a, b)` means that module `a` imports module `b`. -/
def projectImports : Array (String × String) := #[
  ("m001", "m055"), ("m001", "m053"), ("m001", "m024"), ("m001", "m023"), ("m001", "m033"),
    ("m001", "m058"), ("m001", "m039"), ("m001", "m042"), ("m001", "m060"), ("m001", "m002"),
    ("m002", "m003"), ("m002", "m004"), ("m002", "m009"), ("m002", "m008"), ("m002", "m005"),
    ("m002", "m007"), ("m002", "m006"), ("m003", "m034"), ("m004", "m039"), ("m004", "m033"),
    ("m004", "m036"), ("m005", "m009"), ("m006", "m009"), ("m007", "m005"), ("m007", "m008"),
    ("m007", "m067"), ("m008", "m004"), ("m008", "m065"), ("m009", "m003"), ("m009", "m004"),
    ("m010", "m059"), ("m014", "m059"), ("m019", "m059"), ("m022", "m037"), ("m023", "m022"),
    ("m023", "m021"), ("m024", "m027"), ("m024", "m030"), ("m024", "m029"), ("m024", "m025"),
    ("m024", "m026"), ("m024", "m028"), ("m024", "m055"), ("m025", "m038"), ("m025", "m030"),
    ("m026", "m035"), ("m027", "m035"), ("m028", "m038"), ("m028", "m035"), ("m028", "m049"),
    ("m029", "m032"), ("m030", "m032"), ("m030", "m049"), ("m031", "m022"), ("m031", "m037"),
    ("m031", "m052"), ("m032", "m035"), ("m033", "m022"), ("m033", "m036"), ("m033", "m011"),
    ("m033", "m018"), ("m035", "m031"), ("m036", "m034"), ("m036", "m059"), ("m036", "m012"),
    ("m036", "m013"), ("m036", "m057"), ("m037", "m036"), ("m037", "m047"), ("m038", "m031"),
    ("m039", "m046"), ("m039", "m041"), ("m039", "m043"), ("m039", "m044"), ("m039", "m045"),
    ("m041", "m040"), ("m041", "m058"), ("m042", "m039"), ("m042", "m033"), ("m043", "m040"),
    ("m043", "m058"), ("m044", "m046"), ("m045", "m040"), ("m045", "m044"), ("m046", "m040"),
    ("m047", "m059"), ("m048", "m049"), ("m049", "m054"), ("m050", "m047"), ("m051", "m056"),
    ("m052", "m047"), ("m053", "m021"), ("m053", "m052"), ("m054", "m051"), ("m055", "m048"),
    ("m056", "m050"), ("m056", "m052"), ("m056", "m057"), ("m057", "m014"), ("m057", "m010"),
    ("m057", "m017"), ("m057", "m019"), ("m057", "m020"), ("m060", "m066"), ("m060", "m062"),
    ("m060", "m064"), ("m060", "m068"), ("m060", "m061"), ("m060", "m070"), ("m060", "m071"),
    ("m060", "m063"), ("m060", "m065"), ("m060", "m067"), ("m060", "m069"), ("m061", "m039"),
    ("m061", "m066"), ("m061", "m062"), ("m061", "m034"), ("m062", "m016"), ("m062", "m015"),
    ("m063", "m071"), ("m064", "m066"), ("m065", "m071"), ("m066", "m033"), ("m067", "m071"),
    ("m067", "m042"), ("m068", "m064"), ("m069", "m068"), ("m069", "m062"), ("m070", "m066"),
    ("m071", "m070"), ("m071", "m061"), ("m071", "m068"), ("m071", "m024"), ("m071", "m033"),
    ("m072", "m006"), ("m073", "m001"), ("m074", "m001"), ("m075", "m001"), ("m076", "m074"),
    ("m077", "m039"), ("m077", "m042"), ("m077", "m021"), ("m077", "m074"), ("m078", "m039"),
    ("m079", "m063"), ("m079", "m065"), ("m079", "m082"), ("m080", "m062"), ("m080", "m077"),
    ("m081", "m001"), ("m082", "m068"), ("m082", "m077"), ("m083", "m001"), ("m083", "m081"),
    ("m083", "m074"), ("m083", "m075"), ("m083", "m077"), ("m083", "m086"), ("m083", "m082"),
    ("m083", "m080"), ("m083", "m079"), ("m083", "m087"), ("m083", "m078"), ("m083", "m073"),
    ("m084", "m001"), ("m085", "m069"), ("m086", "m021"), ("m086", "m074"), ("m086", "m077"),
    ("m087", "m060"), ("m087", "m079"), ("m088", "m087")]

/-- The import edges between the modules of this library and its tests: `(a, b)` means that
module `a` imports module `b`. -/
def ownImports : Array (String × String) := #[
  ("PILean", "PILean.Color"), ("PILean", "PILean.Geometry"), ("PILean", "PILean.Path"),
    ("PILean", "PILean.Svg"), ("PILean", "PILean.Png"), ("PILean", "PILean.Anim"),
    ("PILean", "PILean.Text.Engine"), ("PILean", "PILean.Style"), ("PILean", "PILean.Canvas"),
    ("PILean", "PILean.Image.Basic"), ("PILean", "PILean.Image.Ops"),
    ("PILean", "PILean.Image.Proofs"), ("PILean", "PILean.Exact"),
    ("PILean", "PILean.Plot.Ticks"), ("PILean", "PILean.Plot.Scale"),
    ("PILean", "PILean.Plot.Sample"), ("PILean", "PILean.Plot.Figure"),
    ("PILean", "PILean.Plot.Proofs"), ("PILean", "PILean.Plot.Exact"),
    ("PILean", "PILean.Graph.Model"), ("PILean", "PILean.Graph.Layout"),
    ("PILean", "PILean.Graph.Layering"), ("PILean", "PILean.Graph.Ordering"),
    ("PILean", "PILean.Graph.Coordinates"), ("PILean", "PILean.Graph.Layered"),
    ("PILean", "PILean.Graph.Simple"), ("PILean", "PILean.Graph.Draw"),
    ("PILean", "PILean.Graph.Proofs"), ("PILean", "PILean.Graph.Spec"),
    ("PILean", "PILean.Raster.Coverage"), ("PILean", "PILean.Raster.Canvas"),
    ("PILean", "PILean.Raster.Stroke"), ("PILean", "PILean.Raster.Draw"),
    ("PILean", "PILean.Raster.SvgRender"), ("PILean", "PILean.Raster.Proofs"),
    ("PILean", "PILean.Trust.Sha256"), ("PILean", "PILean.Trust.Sha256Proofs"),
    ("PILean", "PILean.Trust.Provenance"), ("PILean", "PILean.Trust.Figure"),
    ("PILean", "PILean.Trust.Fingerprint"), ("PILean", "PILean.Trust.Json"),
    ("PILean", "PILean.Trust.Manifest"), ("PILean", "PILean.Trust.Build"),
    ("PILean", "PILean.Trust.Verify"), ("PILean", "PILean.Version"),
    ("PILean.Anim", "PILean.Anim.Frames"), ("PILean.Anim", "PILean.Anim.Compose"),
    ("PILean.Anim", "PILean.Anim.Apng"), ("PILean.Anim", "PILean.Anim.ApngRead"),
    ("PILean.Anim", "PILean.Anim.Lzw"), ("PILean.Anim", "PILean.Anim.Quantize"),
    ("PILean.Anim", "PILean.Anim.Gif"), ("PILean.Anim", "PILean.Anim.GifRead"),
    ("PILean.Anim", "PILean.Anim.Animation"), ("PILean.Anim", "PILean.Anim.Proofs"),
    ("PILean.Anim.Animation", "PILean.Anim.Apng"), ("PILean.Anim.Animation", "PILean.Anim.Gif"),
    ("PILean.Anim.Animation", "PILean.Canvas"), ("PILean.Anim.Animation", "PILean.Exact"),
    ("PILean.Anim.Apng", "PILean.Anim.Frames"), ("PILean.Anim.Apng", "PILean.Png"),
    ("PILean.Anim.ApngRead", "PILean.Anim.Compose"),
    ("PILean.Anim.Compose", "PILean.Anim.Frames"), ("PILean.Anim.Frames", "PILean.Image.Basic"),
    ("PILean.Anim.Gif", "PILean.Anim.Frames"), ("PILean.Anim.Gif", "PILean.Anim.Lzw"),
    ("PILean.Anim.Gif", "PILean.Anim.Quantize"), ("PILean.Anim.GifRead", "PILean.Anim.Compose"),
    ("PILean.Anim.GifRead", "PILean.Anim.Lzw"), ("PILean.Anim.Lzw", "PILean.Png.Tables"),
    ("PILean.Anim.Proofs", "PILean.Anim.Animation"),
    ("PILean.Anim.Quantize", "PILean.Png.Tables"), ("PILean.Canvas", "PILean.Raster.SvgRender"),
    ("PILean.Canvas", "PILean.Text.Engine"),
    ("PILean.Graph.Coordinates", "PILean.Graph.Ordering"),
    ("PILean.Graph.Draw", "PILean.Graph.Layered"), ("PILean.Graph.Draw", "PILean.Canvas"),
    ("PILean.Graph.Layered", "PILean.Graph.Layout"),
    ("PILean.Graph.Layered", "PILean.Graph.Layering"),
    ("PILean.Graph.Layered", "PILean.Graph.Ordering"),
    ("PILean.Graph.Layered", "PILean.Graph.Coordinates"),
    ("PILean.Graph.Layout", "PILean.Graph.Model"), ("PILean.Graph.Layout", "PILean.Style"),
    ("PILean.Graph.Layout", "PILean.Path"), ("PILean.Graph.Model", "PILean.Color"),
    ("PILean.Graph.Proofs", "PILean.Graph.Layered"),
    ("PILean.Graph.Simple", "PILean.Graph.Layered"),
    ("PILean.Graph.Spec", "PILean.Graph.Proofs"), ("PILean.Graph.Spec", "PILean.Graph.Draw"),
    ("PILean.Image.Basic", "PILean.Color"), ("PILean.Image.Basic", "PILean.Png"),
    ("PILean.Image.Ops", "PILean.Image.Basic"), ("PILean.Image.Proofs", "PILean.Image.Ops"),
    ("PILean.Path", "PILean.Geometry"), ("PILean.Plot.Exact", "PILean.Exact"),
    ("PILean.Plot.Exact", "PILean.Plot.Figure"), ("PILean.Plot.Figure", "PILean.Plot.Scale"),
    ("PILean.Plot.Figure", "PILean.Plot.Sample"), ("PILean.Plot.Figure", "PILean.Canvas"),
    ("PILean.Plot.Figure", "PILean.Style"), ("PILean.Plot.Proofs", "PILean.Plot.Ticks"),
    ("PILean.Plot.Sample", "PILean.Geometry"), ("PILean.Plot.Scale", "PILean.Plot.Ticks"),
    ("PILean.Png", "PILean.Png.Checksum"), ("PILean.Png", "PILean.Png.Tables"),
    ("PILean.Png", "PILean.Png.Deflate"), ("PILean.Png", "PILean.Png.Inflate"),
    ("PILean.Png", "PILean.Png.Types"), ("PILean.Png", "PILean.Png.Write"),
    ("PILean.Png", "PILean.Png.Read"), ("PILean.Png", "PILean.Png.Proofs"),
    ("PILean.Png.Deflate", "PILean.Png.Checksum"), ("PILean.Png.Deflate", "PILean.Png.Tables"),
    ("PILean.Png.Inflate", "PILean.Png.Checksum"), ("PILean.Png.Inflate", "PILean.Png.Tables"),
    ("PILean.Png.Proofs", "PILean.Png.Checksum"), ("PILean.Png.Proofs", "PILean.Png.Deflate"),
    ("PILean.Png.Proofs", "PILean.Png.Inflate"), ("PILean.Png.Read", "PILean.Png.Types"),
    ("PILean.Png.Read", "PILean.Png.Write"), ("PILean.Png.Types", "PILean.Png.Inflate"),
    ("PILean.Png.Write", "PILean.Png.Types"), ("PILean.Png.Write", "PILean.Png.Deflate"),
    ("PILean.Raster.Canvas", "PILean.Raster.Coverage"),
    ("PILean.Raster.Canvas", "PILean.Raster.SrgbTables"),
    ("PILean.Raster.Canvas", "PILean.Image.Basic"), ("PILean.Raster.Coverage", "PILean.Path"),
    ("PILean.Raster.Draw", "PILean.Raster.Canvas"),
    ("PILean.Raster.Draw", "PILean.Raster.Stroke"),
    ("PILean.Raster.Proofs", "PILean.Raster.Canvas"), ("PILean.Raster.Stroke", "PILean.Path"),
    ("PILean.Raster.SvgRender", "PILean.Svg"), ("PILean.Raster.SvgRender", "PILean.Raster.Draw"),
    ("PILean.Style", "PILean.Color"), ("PILean.Style", "PILean.Text.Engine"),
    ("PILean.Svg", "PILean.Path"), ("PILean.Svg", "PILean.Color"),
    ("PILean.Text.Engine", "PILean.Text.Lettering"),
    ("PILean.Text.Lettering", "PILean.Text.LetteringGlyphs"),
    ("PILean.Text.Lettering", "PILean.Text.LetteringLower"),
    ("PILean.Text.Lettering", "PILean.Text.LetteringSymbols"),
    ("PILean.Text.LetteringGlyphs", "PILean.Path"),
    ("PILean.Text.LetteringLower", "PILean.Text.LetteringGlyphs"),
    ("PILean.Text.LetteringSymbols", "PILean.Text.LetteringGlyphs"),
    ("PILean.Trust.Attr", "PILean.Trust.Fingerprint"),
    ("PILean.Trust.Build", "PILean.Trust.Manifest"),
    ("PILean.Trust.Build", "PILean.Trust.Build"), ("PILean.Trust.Figure", "PILean.Plot.Figure"),
    ("PILean.Trust.Figure", "PILean.Graph.Draw"),
    ("PILean.Trust.Figure", "PILean.Anim.Animation"),
    ("PILean.Trust.Fingerprint", "PILean.Trust.Figure"),
    ("PILean.Trust.Fingerprint", "PILean.Trust.Provenance"),
    ("PILean.Trust.Fingerprint", "PILean.Trust.Sha256"),
    ("PILean.Trust.Manifest", "PILean.Trust.Json"),
    ("PILean.Trust.Manifest", "PILean.Trust.Fingerprint"),
    ("PILean.Trust.Provenance", "PILean.Svg"), ("PILean.Trust.Provenance", "PILean.Png"),
    ("PILean.Trust.Provenance", "PILean.Version"),
    ("PILean.Trust.Sha256Proofs", "PILean.Trust.Sha256"),
    ("PILean.Trust.Verify", "PILean.Trust.Manifest"),
    ("PILeanTest.Anim", "PILeanTest.AnimFiles"), ("PILeanTest.AnimData", "PILean"),
    ("PILeanTest.AnimFiles", "PILeanTest.AnimData"), ("PILeanTest.Build", "PILeanTest.Examples"),
    ("PILeanTest.Build", "PILean.Trust.Build"), ("PILeanTest.Color", "PILean.Color"),
    ("PILeanTest.Exact", "PILeanTest.Examples"), ("PILeanTest.Examples", "PILean"),
    ("PILeanTest.Examples", "PILeanTest.Graphs"),
    ("PILeanTest.Examples", "PILeanTest.ProvedExamples"),
    ("PILeanTest.Examples", "PILean.Trust.Attr"), ("PILeanTest.Gallery", "PILeanTest.Examples"),
    ("PILeanTest.Graphs", "PILean"), ("PILeanTest.Image", "PILean"),
    ("PILeanTest.Info", "PILean"), ("PILeanTest.Lettering", "PILean"),
    ("PILeanTest.Lettering", "PILean.Text.Engine"), ("PILeanTest.Main", "PILeanTest.Color"),
    ("PILeanTest.Main", "PILeanTest.Units"), ("PILeanTest.Main", "PILeanTest.Examples"),
    ("PILeanTest.Main", "PILeanTest.Raster"), ("PILeanTest.Main", "PILeanTest.Png"),
    ("PILeanTest.Main", "PILeanTest.Image"), ("PILeanTest.Main", "PILeanTest.Anim"),
    ("PILeanTest.Main", "PILeanTest.Plots"), ("PILeanTest.Main", "PILeanTest.Lettering"),
    ("PILeanTest.Main", "PILeanTest.Graphs"), ("PILeanTest.Main", "PILeanTest.Exact"),
    ("PILeanTest.Main", "PILeanTest.Trust"), ("PILeanTest.Main", "PILeanTest.TrustBuild"),
    ("PILeanTest.Plots", "PILeanTest.Examples"), ("PILeanTest.Png", "PILean"),
    ("PILeanTest.ProvedExamples", "PILean"), ("PILeanTest.ProvedExamples", "PILean.Trust.Attr"),
    ("PILeanTest.Raster", "PILean"), ("PILeanTest.Raster", "PILeanTest.Examples"),
    ("PILeanTest.Trust", "PILean"), ("PILeanTest.Trust", "PILeanTest.AnimData"),
    ("PILeanTest.Trust", "PILeanTest.Examples"), ("PILeanTest.Trust", "PILeanTest.TrustData"),
    ("PILeanTest.TrustBuild", "PILean"), ("PILeanTest.TrustBuild", "PILean.Trust.Attr"),
    ("PILeanTest.TrustBuild", "PILeanTest.Examples"), ("PILeanTest.Units", "PILean"),
    ("PILeanTest.Verify", "PILean.Trust.Verify")]

/-- The dependency graph of a blueprint of 58 nodes (146 edges) in 6 chapters and 13 sections,
as a site generator writes it (names removed): each node as
`(length of its label, chapter, section)`. -/
def blueprintANodes : Array (Nat × Nat × Nat) := #[
  (17, 0, 0), (14, 1, 1), (4, 2, 2), (24, 0, 3), (31, 1, 1), (10, 0, 4), (20, 3, 5), (12, 4, 6),
  (10, 0, 7), (17, 3, 8), (26, 1, 1), (11, 1, 1), (17, 1, 1), (3, 2, 2), (12, 4, 9), (21, 3, 10),
  (19, 1, 1), (14, 0, 4), (17, 4, 6), (9, 5, 11), (16, 5, 11), (16, 0, 7), (17, 4, 12), (19, 1,
  1), (10, 0, 0), (21, 0, 7), (23, 0, 3), (11, 3, 5), (18, 3, 5), (15, 0, 7), (15, 5, 11), (5, 5,
  11), (22, 0, 3), (23, 3, 5), (11, 4, 6), (21, 4, 6), (14, 3, 8), (17, 0, 0), (15, 0, 7), (18, 5,
  11), (10, 4, 12), (10, 0, 7), (27, 3, 10), (12, 5, 11), (16, 1, 1), (28, 0, 3), (15, 3, 5), (4,
  0, 4), (26, 1, 1), (24, 5, 11), (18, 5, 11), (16, 3, 5), (14, 0, 7), (4, 5, 11), (12, 5, 11),
  (17, 1, 1), (13, 0, 7), (14, 3, 5)]

/-- The edges of `blueprintANodes`: `(a, b)` means that `a` is used by `b`. -/
def blueprintAEdges : Array (Nat × Nat) := #[
  (19, 0), (24, 0), (11, 1), (55, 1), (16, 1), (13, 2), (20, 2), (43, 2), (48, 2), (39, 2), (15,
  2), (34, 2), (40, 2), (21, 3), (25, 3), (24, 3), (23, 4), (12, 4), (1, 4), (47, 5), (27, 6),
  (51, 6), (27, 7), (21, 7), (47, 7), (35, 7), (57, 7), (56, 7), (45, 7), (5, 7), (47, 8), (19,
  8), (23, 10), (11, 12), (44, 12), (55, 12), (47, 14), (5, 14), (23, 15), (10, 15), (42, 15),
  (11, 16), (55, 16), (47, 17), (19, 17), (31, 17), (5, 17), (39, 17), (47, 18), (19, 18), (5,
  18), (31, 20), (8, 21), (41, 22), (19, 22), (36, 22), (17, 22), (24, 22), (19, 24), (37, 24),
  (28, 24), (30, 24), (21, 25), (29, 25), (38, 25), (21, 26), (32, 26), (0, 26), (19, 30), (21,
  32), (29, 32), (38, 32), (17, 32), (24, 32), (27, 33), (51, 33), (47, 34), (19, 34), (7, 34),
  (35, 34), (26, 34), (14, 34), (27, 35), (47, 35), (19, 35), (18, 35), (33, 35), (30, 35), (9,
  36), (19, 37), (30, 37), (8, 38), (17, 38), (30, 38), (19, 39), (31, 39), (43, 39), (50, 39),
  (47, 40), (19, 40), (22, 40), (56, 40), (3, 40), (0, 40), (14, 40), (8, 41), (23, 42), (10, 42),
  (31, 43), (50, 43), (11, 44), (55, 44), (21, 45), (25, 45), (24, 45), (38, 45), (29, 45), (23,
  48), (4, 48), (20, 49), (43, 49), (55, 49), (19, 50), (30, 50), (27, 51), (46, 51), (41, 52),
  (21, 52), (25, 52), (24, 52), (28, 52), (31, 53), (53, 54), (20, 54), (49, 54), (11, 55), (41,
  56), (21, 56), (47, 56), (52, 56), (37, 56), (5, 56), (27, 57), (9, 57), (6, 57), (28, 57)]

/-- The chapter of every section of `blueprintANodes`. -/
def blueprintASections : Array Nat := #[0, 1, 2, 0, 0, 3, 4, 0, 3, 4, 3, 5, 4]

/-- The dependency graph of a blueprint of 69 nodes (111 edges) in 8 chapters, one section each,
as a site generator writes it (names removed): each node as
`(length of its label, chapter, section)`. -/
def blueprintBNodes : Array (Nat × Nat × Nat) := #[
  (21, 0, 0), (23, 1, 1), (15, 2, 2), (18, 3, 3), (30, 1, 1), (15, 4, 4), (17, 2, 2), (16, 5, 5),
  (16, 4, 4), (19, 2, 2), (16, 6, 6), (20, 0, 0), (15, 6, 6), (31, 7, 7), (12, 7, 7), (16, 2, 2),
  (12, 6, 6), (13, 2, 2), (12, 4, 4), (8, 5, 5), (20, 1, 1), (14, 0, 0), (10, 3, 3), (15, 5, 5),
  (23, 7, 7), (20, 0, 0), (15, 5, 5), (14, 0, 0), (17, 2, 2), (16, 2, 2), (10, 3, 3), (16, 0, 0),
  (21, 7, 7), (9, 0, 0), (16, 5, 5), (12, 7, 7), (9, 2, 2), (15, 2, 2), (27, 7, 7), (14, 1, 1),
  (12, 2, 2), (16, 5, 5), (16, 7, 7), (12, 3, 3), (17, 3, 3), (19, 4, 4), (16, 2, 2), (11, 2, 2),
  (18, 3, 3), (15, 2, 2), (18, 1, 1), (18, 6, 6), (18, 6, 6), (11, 5, 5), (12, 5, 5), (18, 4, 4),
  (17, 6, 6), (14, 0, 0), (16, 3, 3), (32, 1, 1), (9, 0, 0), (11, 3, 3), (16, 6, 6), (19, 5, 5),
  (14, 2, 2), (16, 6, 6), (22, 6, 6), (14, 2, 2), (14, 0, 0)]

/-- The edges of `blueprintBNodes`: `(a, b)` means that `a` is used by `b`. -/
def blueprintBEdges : Array (Nat × Nat) := #[
  (66, 0), (68, 0), (67, 0), (50, 1), (32, 2), (15, 2), (46, 2), (29, 2), (17, 2), (2, 3), (61,
  3), (48, 3), (20, 4), (50, 4), (18, 5), (36, 6), (26, 7), (18, 8), (35, 9), (4, 9), (57, 11),
  (27, 11), (41, 11), (7, 11), (31, 11), (16, 12), (20, 13), (49, 15), (64, 15), (52, 15), (5,
  15), (40, 17), (6, 17), (12, 17), (17, 21), (60, 21), (3, 22), (1, 22), (24, 22), (54, 23), (14,
  24), (21, 25), (41, 25), (55, 25), (19, 26), (42, 27), (68, 27), (0, 27), (45, 27), (47, 28),
  (37, 29), (56, 29), (44, 30), (11, 30), (25, 30), (33, 30), (68, 31), (41, 31), (35, 32), (38,
  32), (13, 32), (4, 32), (60, 33), (17, 33), (63, 34), (50, 35), (40, 37), (14, 38), (36, 40),
  (16, 40), (19, 41), (35, 42), (57, 43), (21, 43), (43, 44), (8, 45), (50, 45), (64, 46), (9,
  46), (6, 46), (30, 48), (35, 49), (16, 51), (62, 52), (19, 54), (8, 55), (65, 56), (10, 56),
  (68, 57), (0, 57), (60, 58), (47, 60), (58, 61), (17, 61), (28, 61), (12, 62), (23, 63), (41,
  63), (26, 63), (53, 63), (35, 64), (50, 64), (16, 65), (16, 66), (36, 67), (50, 67), (60, 68),
  (16, 68), (12, 68), (40, 68), (42, 68)]

/-- The chapter of every section of `blueprintBNodes`. -/
def blueprintBSections : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7]

end PILeanTest.Fixtures
