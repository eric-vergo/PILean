/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Exact.Plane

/-!
# Specifications of plane figures in exact terms

A figure's specification says which item is which exact object, in which colour, with which
title and which recorded incidences, so that a theorem about the exact numbers (that a point is
on a circle, say) is a theorem about the item that draws them; with the figure's constant in the
statement, `figure_links` links it to the figure.

For an item built with the builders of `PILean.Exact.Plane` and the modifiers, `simp` with the
predicate, the builders and the modifiers used, `Item.mapLook`, `Item.mapInfo` and
`and_assoc, exists_and_left, exists_eq_left'` proves it (`PILeanTest/PlaneExact.lean`,
`reference_spec`, shows the whole proof).

## Main definitions

* `Plane.Exact.IsPoint`, `Plane.Exact.IsDisk`, `Plane.Exact.IsSegment`, `Plane.Exact.IsRegion`.

## Main results

* `Plane.Exact.IsPoint.draw`: an item that is an exact point is drawn as a marker in its tone at
  the frame's image of the point's conversion.
-/

namespace PILean.Plane.Exact

open PILean.Exact Canvas

variable {α β : Type} [PlanePoint α] [RealValue β]

/-- The item is the exact point `p` in the tone `t` with exactly the incidences `rels` recorded
(`Item.incident`): a point item at the conversion of `p`. -/
def IsPoint (it : Item) (p : α) (t : Tone) (rels : Array (Incidence × String)) : Prop :=
  ∃ (l : Look) (i : ShapeInfo), it = .shape (.point (PlanePoint.toPoint p)) l i ∧ l.tone = t ∧
    l.incidences = rels

/-- The item is the closed disk with the exact centre `c` and radius `r`, in the tone `t`, with
the title `title` (the name incidences refer to it by). -/
def IsDisk (it : Item) (c : α) (r : β) (t : Tone) (title : String) : Prop :=
  ∃ (l : Look) (i : ShapeInfo),
    it = .shape (.disk (PlanePoint.toPoint c) (RealValue.toFloat r)) l i ∧ l.tone = t ∧
      i.title = title

/-- The item is the segment between the exact points `a` and `b`, in the tone `t`, with the title
`title`. -/
def IsSegment (it : Item) (a b : α) (t : Tone) (title : String) : Prop :=
  ∃ (l : Look) (i : ShapeInfo),
    it = .shape (.segment (PlanePoint.toPoint a) (PlanePoint.toPoint b)) l i ∧ l.tone = t ∧
      i.title = title

/-- The item is the region `op` of the closed disks `(c₁, r₁)` and `(c₂, r₂)` with exact centres
and radii (a lens for `.intersection`), in the tone `t`, with the title `title`. -/
def IsRegion (it : Item) (op : RegionOp) (c₁ c₂ : α) (r₁ r₂ : β) (t : Tone) (title : String) :
    Prop :=
  ∃ (l : Look) (i : ShapeInfo),
    it = .shape (.disks op (PlanePoint.toPoint c₁) (RealValue.toFloat r₁) (PlanePoint.toPoint c₂)
      (RealValue.toFloat r₂)) l i ∧ l.tone = t ∧ i.title = title

/-- An item that is the exact point `p` in the tone `t` is drawn as a marker in that tone at the
frame's image of the conversion of `p` (inside a group with its metadata when it has some). -/
theorem IsPoint.draw {it : Item} {p : α} {t : Tone} {rels : Array (Incidence × String)}
    (h : IsPoint it p t rels) (e : Env) :
    ∃ (l : Look) (i : ShapeInfo), l.tone = t ∧ drawItem e it =
      if i.isEmpty then e.marker l (e.frame.toScreen (PlanePoint.toPoint p))
      else #[.tagged i (.group (e.marker l (e.frame.toScreen (PlanePoint.toPoint p))))] := by
  obtain ⟨l, i, rfl, ht, _⟩ := h
  exact ⟨l, i, ht, drawItem_point e _ l i⟩

/-- The hypotheses can be met: the point `(1, 2)` in accent 0, recorded on the element titled
`"c"`, is such an item. -/
example : IsPoint ((point ((1, 2) : Int × Int)).accent 0 |>.incident .on "c") ((1, 2) : Int × Int)
    (.accent 0) #[(.on, "c")] := by
  simp [IsPoint, point, Plane.point, Item.incident, Item.accent, Item.tone, Item.mapLook,
    Item.mapInfo]

end PILean.Plane.Exact
