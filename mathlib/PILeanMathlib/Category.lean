/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.EqToHom
import PILean.Diagram.CommDiagram

/-!
# Commutative diagrams in a category

A `CommDiagram` of PILean is plain data: labels, arrows between object numbers, and claims that
two paths of arrows compose to the same morphism. Here a *realisation* of it in a category `C`
(`CommDiagram.Realisation`) gives each object an object of `C` and each arrow a morphism of `C`
between the objects of its ends, so that the statement that the drawing commutes is a statement
about those morphisms:

* `Realisation.pathHom`: the composite of a path of arrows, when its arrows follow one another;
* `Realisation.Commutes`: every claim's two paths compose to the same morphism;
* `Realisation.StylesHold`: every arrow drawn as a monomorphism (`↣`) or an inclusion (`↪`) is a
  `Mono`, every arrow drawn as an epimorphism (`↠`) an `Epi`, every arrow drawn with `≅` an
  `IsIso`, and every arrow drawn as `=` an identity (`eqToHom`), so that no mark of the picture
  claims what the morphisms do not satisfy.

For the three shapes of the gallery the realisation is built from Mathlib's objects and the
condition is Mathlib's own:

* `square_commutes_iff`: the square of `f`, `g`, `h`, `i` commutes exactly when `CommSq f g h i`;
* `triangle_commutes_iff`: the triangle of `f`, `g`, `h` commutes exactly when `f ≫ g = h`;
* `shortExact_iff`: the drawing `0 → X₁ ↣ X₂ ↠ X₃ → 0` of a short complex `S` has its marks
  justified and `S` exact exactly when `S.ShortExact`.
-/

namespace PILean.Diagram

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CommDiagram

/-- A realisation of the diagram `D` in the category `C`: an object for each object number and,
for each arrow, a morphism from the object of its source to the object of its target. -/
structure Realisation (D : CommDiagram) (C : Type*) [Category C] where
  /-- The object of each object number. -/
  obj : ℕ → C
  /-- The morphism of each arrow. -/
  mor : (k : Fin D.arrows.length) → (obj D.arrows[k].src ⟶ obj D.arrows[k].tgt)

variable {C : Type*} [Category C] {D : CommDiagram}

namespace Realisation

/-- The composite of the path of arrows `p` from object `i` to object `j`: `none` unless each
arrow starts where the previous one ends, the first at `i` and the last ending at `j` (the empty
path from `i` to `i` is the identity). -/
def pathHom (R : Realisation D C) : List ℕ → (i j : ℕ) → Option (R.obj i ⟶ R.obj j)
  | [], i, j => if h : i = j then some (eqToHom (congrArg R.obj h)) else none
  | k :: p, i, j =>
    if hk : k < D.arrows.length then
      if h : D.arrows[k].src = i then
        (R.pathHom p D.arrows[k].tgt j).map fun r =>
          eqToHom (congrArg R.obj h.symm) ≫ R.mor ⟨k, hk⟩ ≫ r
      else none
    else none

/-- The realisation makes the diagram commute: for every claim `(i, p, q)` there is an object
`j` at which both paths end, and their composites are equal. -/
def Commutes (R : Realisation D C) : Prop :=
  ∀ c ∈ D.paths, ∃ j f, R.pathHom c.2.1 c.1 j = some f ∧ R.pathHom c.2.2 c.1 j = some f

/-- The marks of the arrows' styles are true of their morphisms: `↣` and `↪` are monomorphisms,
`↠` epimorphisms, `≅` isomorphisms, and `=` identities. -/
def StylesHold (R : Realisation D C) : Prop :=
  ∀ k : Fin D.arrows.length,
    (D.arrows[k].style = .mono → Mono (R.mor k)) ∧
    (D.arrows[k].style = .inclusion → Mono (R.mor k)) ∧
    (D.arrows[k].style = .epi → Epi (R.mor k)) ∧
    (D.arrows[k].style = .iso → IsIso (R.mor k)) ∧
    (D.arrows[k].style = .equality →
      ∃ h : R.obj D.arrows[k].src = R.obj D.arrows[k].tgt, R.mor k = eqToHom h)

end Realisation

/-! ### A commutative square -/

/-- The square `W → X`, `W → Y`, `X → Z`, `Y → Z` with object labels `obs` (top left, top right,
bottom left, bottom right) and arrow labels `ls` (top, left, right, bottom), claiming that the two
paths from the top left to the bottom right agree. -/
def square (obs : Array String) (ls : Array String) : CommDiagram where
  objects := obs
  pos := #[(0, 0), (1, 0), (0, -1), (1, -1)]
  arrows := [{ src := 0, tgt := 1, label := ls.getD 0 "" },
    { src := 0, tgt := 2, label := ls.getD 1 "", swap := true },
    { src := 1, tgt := 3, label := ls.getD 2 "" },
    { src := 2, tgt := 3, label := ls.getD 3 "", swap := true }]
  paths := [(0, [0, 2], [1, 3])]

/-- The realisation of the square by `f : W ⟶ X`, `g : W ⟶ Y`, `h : X ⟶ Z`, `i : Y ⟶ Z`. -/
def squareRealisation (obs ls : Array String) {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z)
    (i : Y ⟶ Z) : Realisation (square obs ls) C where
  obj n := [W, X, Y, Z].getD n W
  mor k := match k with
    | ⟨0, _⟩ => f
    | ⟨1, _⟩ => g
    | ⟨2, _⟩ => h
    | ⟨3, _⟩ => i

/-- The square commutes in the sense of the drawing exactly when it is a `CommSq`. -/
theorem square_commutes_iff (obs ls : Array String) {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y)
    (h : X ⟶ Z) (i : Y ⟶ Z) :
    (squareRealisation obs ls f g h i).Commutes ↔ CommSq f g h i := by
  simp only [Realisation.Commutes, square, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq]
  constructor
  · rintro ⟨j, k, h₁, h₂⟩
    by_cases hj : j = 3
    · subst hj
      simp only [Realisation.pathHom, squareRealisation] at h₁ h₂
      replace h₁ : 𝟙 W ≫ f ≫ 𝟙 X ≫ h ≫ 𝟙 Z = k := Option.some.inj h₁
      replace h₂ : 𝟙 W ≫ g ≫ 𝟙 Y ≫ i ≫ 𝟙 Z = k := Option.some.inj h₂
      simp only [Category.id_comp, Category.comp_id] at h₁ h₂
      exact ⟨h₁.trans h₂.symm⟩
    · simp [Realisation.pathHom, squareRealisation, Ne.symm hj] at h₁
  · intro hsq
    refine ⟨3, f ≫ h, ?_, ?_⟩
    · simp only [Realisation.pathHom, squareRealisation]
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, dite_true, Option.map_some]
      change some (𝟙 W ≫ f ≫ 𝟙 X ≫ h ≫ 𝟙 Z) = some (f ≫ h)
      simp
    · simp only [Realisation.pathHom, squareRealisation]
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, dite_true, Option.map_some]
      change some (𝟙 W ≫ g ≫ 𝟙 Y ≫ i ≫ 𝟙 Z) = some (f ≫ h)
      simp [hsq.w]

/-! ### A commutative triangle -/

/-- The triangle `X → Y → Z` with the diagonal `X → Z`, object labels `obs` and arrow labels `ls`
(`X → Y`, `Y → Z`, `X → Z`), claiming that the two paths from `X` to `Z` agree. -/
def triangle (obs : Array String) (ls : Array String) : CommDiagram where
  objects := obs
  pos := #[(0, 0), (1, 0), (1, -1)]
  arrows := [{ src := 0, tgt := 1, label := ls.getD 0 "" },
    { src := 1, tgt := 2, label := ls.getD 1 "" },
    { src := 0, tgt := 2, label := ls.getD 2 "", swap := true }]
  paths := [(0, [0, 1], [2])]

/-- The realisation of the triangle by `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : X ⟶ Z`. -/
def triangleRealisation (obs ls : Array String) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) : Realisation (triangle obs ls) C where
  obj n := [X, Y, Z].getD n X
  mor k := match k with
    | ⟨0, _⟩ => f
    | ⟨1, _⟩ => g
    | ⟨2, _⟩ => h

/-- The triangle commutes exactly when `f ≫ g = h`. -/
theorem triangle_commutes_iff (obs ls : Array String) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) : (triangleRealisation obs ls f g h).Commutes ↔ f ≫ g = h := by
  simp only [Realisation.Commutes, triangle, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq]
  constructor
  · rintro ⟨j, k, h₁, h₂⟩
    by_cases hj : j = 2
    · subst hj
      simp only [Realisation.pathHom, triangleRealisation] at h₁ h₂
      replace h₁ : 𝟙 X ≫ f ≫ 𝟙 Y ≫ g ≫ 𝟙 Z = k := Option.some.inj h₁
      replace h₂ : 𝟙 X ≫ h ≫ 𝟙 Z = k := Option.some.inj h₂
      simp only [Category.id_comp, Category.comp_id] at h₁ h₂
      exact h₁.trans h₂.symm
    · simp [Realisation.pathHom, triangleRealisation, Ne.symm hj] at h₁
  · intro hfg
    refine ⟨2, f ≫ g, ?_, ?_⟩
    · simp only [Realisation.pathHom, triangleRealisation]
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, dite_true, Option.map_some]
      change some (𝟙 X ≫ f ≫ 𝟙 Y ≫ g ≫ 𝟙 Z) = some (f ≫ g)
      simp
    · simp only [Realisation.pathHom, triangleRealisation]
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, dite_true, Option.map_some]
      change some (𝟙 X ≫ h ≫ 𝟙 Z) = some (f ≫ g)
      simp [hfg]

/-! ### A short exact sequence -/

/-- The drawing `0 → X₁ ↣ X₂ ↠ X₃ → 0` of a short complex, left to right, with the object labels
`obs` (`X₁`, `X₂`, `X₃`) and the labels `lf`, `lg` of its two maps. -/
def shortExact (obs : Array String) (lf lg : String) : CommDiagram where
  objects := #["0", obs.getD 0 "", obs.getD 1 "", obs.getD 2 "", "0"]
  pos := #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]
  arrows := [{ src := 0, tgt := 1 }, { src := 1, tgt := 2, label := lf, style := .mono },
    { src := 2, tgt := 3, label := lg, style := .epi }, { src := 3, tgt := 4 }]

variable [Preadditive C] [HasZeroObject C]

/-- The realisation of the drawing by the short complex `S`: the zero object at both ends, the
zero maps from and to it, and `S.f`, `S.g`. -/
noncomputable def shortExactRealisation (obs : Array String) (lf lg : String)
    (S : ShortComplex C) : Realisation (shortExact obs lf lg) C where
  obj n := [0, S.X₁, S.X₂, S.X₃, 0].getD n 0
  mor k := match k with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => S.f
    | ⟨2, _⟩ => S.g
    | ⟨3, _⟩ => 0

/-- The marks of the drawing of `S` (`S.f` a monomorphism, `S.g` an epimorphism) hold and `S` is
exact exactly when `S` is short exact. -/
theorem shortExact_iff (obs : Array String) (lf lg : String) (S : ShortComplex C) :
    (shortExactRealisation obs lf lg S).StylesHold ∧ S.Exact ↔ S.ShortExact := by
  constructor
  · rintro ⟨hs, hex⟩
    have hf : Mono S.f := (hs ⟨1, by simp [shortExact]⟩).1 rfl
    have hg : Epi S.g := (hs ⟨2, by simp [shortExact]⟩).2.2.1 rfl
    exact ⟨hex⟩
  · intro h
    refine ⟨fun k => ?_, h.exact⟩
    have hf := h.mono_f
    have hg := h.epi_g
    match k with
    | ⟨0, _⟩ => simp [shortExact]
    | ⟨1, _⟩ => exact ⟨fun _ => hf, by simp [shortExact], by simp [shortExact],
        by simp [shortExact], by simp [shortExact]⟩
    | ⟨2, _⟩ => exact ⟨by simp [shortExact], by simp [shortExact], fun _ => hg,
        by simp [shortExact], by simp [shortExact]⟩
    | ⟨3, _⟩ => simp [shortExact]

end CommDiagram

end PILean.Diagram
