/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Light and dark outputs

A page with a light and a dark theme shows each figure in the colours of the theme in use.
`SiteOutputs α` says which files a figure of type `α` is rendered to for a site: the light files
PILean's `ToOutputs` gives, and, for the types whose colours come from a `Style` (plots, plane
figures, graphs and motions of plane figures), the same files drawn in the dark style, with the
suffix `-dark` after the light file's suffix (`-key-2` becomes `-key-2-dark`).

A page shows a motion's moving picture inline, restyled in the dark theme by its own rules
(`PILeanVersoManual.Inline`); its dark files are the key stills, the poster and the contact sheet
that the page shows as pictures, and the dark animated SVG offered with them. The dark motion is
the motion with every key drawn in the dark style (`Plane.Motion.withStyle`), checked as the light
one is: an error of the dark motion fails its files as one of the light motion fails theirs.

A figure is drawn dark only when its style uses the light colours (`Style.darkVariant?`): an
author who chose other colours chose them for one background, and the site shows that figure in
both themes as it is.

## Main definitions

* `Style.darkVariant?`: the dark counterpart of a style in the light colours
* `SiteOutputs`: the files of a figure for a site, with instances for `Plot.Figure`,
  `Plane.Figure`, `Diagram.Diagram`, `GraphFigure`, `Graph`, `Plane.Motion` and
  `Plane.MotionPanels`, and a fallback through `ToOutputs`
-/

namespace PILeanVerso

open PILean PILean.Trust

/-- The style `s` with the colours of `Style.dark`, everything else kept, if `s` has the colours of
`Style.light`; `none` otherwise (PILean's `Style.darkTwin?`). -/
def Style.darkVariant? (s : Style) : Option Style := s.darkTwin?

/-- The outputs `os` for the dark theme: the suffix `-dark` added to each name. -/
def darkOutputs (os : Array Output) : Array Output :=
  os.map fun o => { o with name := o.name ++ "-dark" }

/-- The files a figure is rendered to for a site, in a fixed order: the light files first, then
the dark ones (names ending in `-dark`) when the type has them. -/
class SiteOutputs (α : Type) where
  /-- The files of a value. -/
  siteOutputs : α → Array Output

/-- Any renderable value: its `ToOutputs` files, in one theme. -/
instance (priority := low) {α : Type} [ToOutputs α] : SiteOutputs α where
  siteOutputs := ToOutputs.outputs

/-- A plot: its files, and the same in the dark style when it has the light colours. -/
instance : SiteOutputs Plot.Figure where
  siteOutputs fig :=
    ToOutputs.outputs fig ++
      match Style.darkVariant? fig.style with
      | some d => darkOutputs (ToOutputs.outputs { fig with style := d })
      | none => #[]

/-- A plane figure: its files, and the same in the dark style when it has the light colours. -/
instance : SiteOutputs Plane.Figure where
  siteOutputs fig :=
    ToOutputs.outputs fig ++
      match Style.darkVariant? fig.style with
      | some d => darkOutputs (ToOutputs.outputs { fig with style := d })
      | none => #[]

/-- A diagram (a Hasse diagram, a commutative diagram, a Young diagram, …): its files, and the same
in the dark style when it has the light colours. -/
instance : SiteOutputs Diagram.Diagram where
  siteOutputs d :=
    ToOutputs.outputs d ++
      match Style.darkVariant? d.style with
      | some s => darkOutputs (ToOutputs.outputs { d with style := s })
      | none => #[]

/-- A graph figure: its files, and the same in the dark style when it has the light colours. -/
instance : SiteOutputs GraphFigure where
  siteOutputs f :=
    ToOutputs.outputs f ++
      match Style.darkVariant? f.style with
      | some d => darkOutputs (ToOutputs.outputs { f with style := d })
      | none => #[]

/-- A graph, with the default layout and the light style, and in the dark style. -/
instance : SiteOutputs Graph where
  siteOutputs g := SiteOutputs.siteOutputs ({ graph := g } : GraphFigure)

/-- A motion of plane figures: its files, and the same in the dark style when its keys have the
light colours (`Plane.Motion.withStyle`, `Plane.Motion.style`). -/
instance : SiteOutputs Plane.Motion where
  siteOutputs m :=
    ToOutputs.outputs m ++
      match Style.darkVariant? m.style with
      | some d => darkOutputs (ToOutputs.outputs (m.withStyle d))
      | none => #[]

/-- A picture of several motions as panels: its files, and the same in the dark style when its
panels have the light colours (`Plane.MotionPanels.withStyle`). -/
instance : SiteOutputs Plane.MotionPanels where
  siteOutputs P :=
    ToOutputs.outputs P ++
      match Style.darkVariant? P.style with
      | some d => darkOutputs (ToOutputs.outputs (P.withStyle d))
      | none => #[]

end PILeanVerso
