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
figures and graphs), the same files drawn in the dark style, with the suffix `-dark`.

A figure is drawn dark only when its style uses the light colours (`Style.darkVariant?`): an
author who chose other colours chose them for one background, and the site shows that figure in
both themes as it is.

## Main definitions

* `Style.darkVariant?`: the dark counterpart of a style in the light colours
* `SiteOutputs`: the files of a figure for a site, with instances for `Plot.Figure`,
  `Plane.Figure`, `GraphFigure` and `Graph`, and a fallback through `ToOutputs`
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

end PILeanVerso
