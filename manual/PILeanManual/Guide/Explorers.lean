/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanTest.Explorers
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Explorers" =>
%%%
tag := "explorers"
%%%

```lean -show
namespace PILeanManual.ExplorersGuide
open PILean PILean.Diagram PILeanTest.Explorers
```

An {name}`PILean.Explorer` shows a figure as a function of one or two parameters over a finite grid
of values. Every frame is computed in Lean when the explorer is built, and the page only swaps
the frames it was given: there is no computation in the page, so what it shows is what the build
drew, frame by frame. A parameter is an {name}`PILean.ExplorerParam`: a name, its values in order
and how a value is written. {name}`PILean.Explorer.family` makes the frames of one parameter
(played with previous, play and next, and a slider), {name}`PILean.Explorer.family₂` those of two
(the first on a slider, the second played and on a slider of its own):

```lean
/-- A regular polygon with `k` sides inscribed in a circle of radius `r`. -/
def polygonAt (k : Nat) (r : Float) : Plane.Figure :=
  { width := 240, items := #[Plane.regularPolygon ⟨0, 0⟩ r k] }

/-- Polygons of 3 to 6 sides, the radius from 1/2 to 1. -/
def polygons : Explorer :=
  Explorer.family₂ { name := "k", values := #[3, 4, 5, 6], label := toString }
    { name := "r", values := #[0.5, 0.75, 1], label := toString }
    fun k r => ExplorerFrame.ofPlane (polygonAt k r)
```

```lean (name := explorerEx)
#eval (polygons.frames.size, polygons.values, polygons.steps, polygons.valid)
#eval polygons.frameName 7
```

```leanResult explorerEx
```

Every frame of the family is the function at its point of the grid, axis-major
({name}`PILean.Explorer.family₂_frames`), and every point has its frame
({name}`PILean.Explorer.mem_family₂_frames`).

# On a Page
%%%
tag := "explorer-page"
%%%

`:::figure_explorer` puts every frame of an explorer into the page as inline SVG and shows one at
a time. The controls are plain HTML: a slider for each parameter (operable with the arrow keys,
each naming its value to a screen reader), previous, play and next for the played one, and zoom.
The site's script (`pilean-explorer.js`: no network, no `eval`, no `innerHTML`) only switches
which frame is shown, so the page works under a content policy that allows the site's own
scripts and no other. A reader who asks for reduced motion gets no play button; with scripts off
the poster frame is shown first, across the width, and the other frames follow it.

Every frame is a file of the figures folder with its own source record, listed in the manifest
with its SHA-256 and fingerprint (`-frame-k`), so `pilean-verify` checks every picture the page can
show, and the site's check ties each inline frame to its file. An explorer has at most
{name}`PILean.Explorer.maxFrames` frames, and its frames' SVG together at most
{name}`PILean.Explorer.maxBytes` bytes; a build refuses one beyond either.

# Two Explorers with Linked Theorems
%%%
tag := "explorer-proved"
%%%

An explorer's standing comes, as a figure's does, from a theorem linked by `figure_links` whose
statement names it. For a family the theorem is quantified over the grid: it says that the
explorer is the family of its frames and that at every point of the grid the frame's figure is
faithful to its object.

:::figure_explorer PILeanTest.Explorers.cayleyExplorer (label := "cayley-explorer") (alt := "The Cayley graph of the integers modulo n for one generator a: n dots on a circle, numbered from 0, with an arrow from each g to g + a modulo n; n from 5 to 12 on a slider, a from 1 to 4 played. The arrows form gcd(n, a) cycles; when 2a is a multiple of n they are lines joining pairs.") (links := PILeanTest.Explorers.cayleyExplorer_spec)
The Cayley graph of `ℤ/n` for the generator `a`.
:::

{docstring PILeanTest.Explorers.cayleyExplorer_spec}

:::figure_explorer PILeanTest.Explorers.latticeExplorer (label := "lattice-explorer") (alt := "The lattice spanned by (1, 0) and (x, y) in the window from -3 to 3 by -2 to 2, its points as dots and its fundamental parallelogram outlined; x from 0 to 3/4 on a slider, y from 1/2 to 1 played.") (links := PILeanTest.Explorers.latticeExplorer_spec)
The lattice `ℤ (1, 0) + ℤ (x, y)` as its second period moves.
:::

{docstring PILeanTest.Explorers.latticeExplorer_spec}

The optional package `pilean-mathlib` states both families in Mathlib's terms, frame by frame:
the arrows of the frame of `(n, a)` join `s` to `t` exactly when `t = s + a` in `ZMod n`, and
the dots of the frame of `(x, y)` are exactly the points of `Submodule.span ℤ {(1, 0), (x, y)}` in
the window, each once (`cayleyExplorer_zmod` and `latticeExplorer_span`, in
`PILeanMathlib.Examples`).
