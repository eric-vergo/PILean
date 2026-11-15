/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.Examples.Sine

/-!
# The axioms of the theorems

Every theorem of this library depends on `propext`, `Classical.choice` and `Quot.sound` and on no
other axiom. Each check below fails, and with it the build, if that changes: a `sorry` or a
`native_decide` in a proof would add an axiom to the list.
-/

/--
info: 'PILean.exists_chord_sub_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.exists_chord_sub_eq

/--
info: 'PILean.abs_chord_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.abs_chord_sub_le

/--
info: 'PILean.abs_chord_sub_le_of_deriv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.abs_chord_sub_le_of_deriv

/--
info: 'PILean.getElem_mem_polyline' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.getElem_mem_polyline

/--
info: 'PILean.IsVerticallyWithin.mono' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.IsVerticallyWithin.mono

/--
info: 'PILean.IsVerticallyWithin.exists_abs_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.IsVerticallyWithin.exists_abs_sub_le

/--
info: 'PILean.IsVerticallyWithin.hausdorffDist_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.IsVerticallyWithin.hausdorffDist_le

/--
info: 'PILean.Exact.getElem_realSamples' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.getElem_realSamples

/--
info: 'PILean.Exact.cast_gridPoint' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.cast_gridPoint

/--
info: 'PILean.Exact.cast_mem_Icc_of_mem_grid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.cast_mem_Icc_of_mem_grid

/--
info: 'PILean.Exact.isVerticallyWithin_plot' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.isVerticallyWithin_plot

/--
info: 'PILeanMathlib.abs_sin_sub_taylor_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILeanMathlib.abs_sin_sub_taylor_le

/--
info: 'PILeanMathlib.Examples.cast_sineTaylor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILeanMathlib.Examples.cast_sineTaylor

/--
info: 'PILeanMathlib.Examples.abs_sineTaylor_sub_sin_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILeanMathlib.Examples.abs_sineTaylor_sub_sin_le

/--
info: 'PILeanMathlib.Examples.sineFigure_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILeanMathlib.Examples.sineFigure_spec

/--
info: 'PILean.Exact.isVerticallyWithin_plot_of_deriv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.isVerticallyWithin_plot_of_deriv

/--
info: 'PILean.mem_polyline_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.mem_polyline_iff

/--
info: 'PILean.Exact.length_realSamples' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.length_realSamples

/--
info: 'PILean.Exact.gridPoint_mem_grid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PILean.Exact.gridPoint_mem_grid
