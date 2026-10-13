import Mathlib

namespace BertsekasShreve.AnalyticSelection

open MeasureTheory

/-- **Definition 7.21** (p. 177). Let `D ⊆ X` and `f : D → R*`. `f` is *lower semianalytic* if
`D` is analytic and `{x ∈ D | f(x) < c}` is analytic for every real `c`. -/
def IsLowerSemianalytic {X : Type*} [TopologicalSpace X] (D : Set X) (f : D → EReal) : Prop :=
  AnalyticSet D ∧ ∀ c : ℝ, AnalyticSet (Subtype.val '' {x : D | f x < (c : EReal)})

/-- Eq. (103) / (114) of Chapter 7 (pp. 180, 184). For `D ⊆ X × Y` and `f : D → R*`, the
partial infimum `f* : proj_X(D) → R*`, `f*(x) = inf_{y ∈ D_x} f(x, y)`, where
`D_x = {y | (x, y) ∈ D}`. -/
noncomputable def partialInf {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) :
    (Prod.fst '' D) → EReal :=
  fun x => ⨅ (y : Y) (h : ((x : X), y) ∈ D), f ⟨((x : X), y), h⟩

/-- The set `I` of Proposition 7.50(b) (p. 185): the points `x ∈ proj_X(D)` at which the
infimum `f*(x)` is attained, i.e. `f(x, y_x) = f*(x)` for some `y_x ∈ D_x`. -/
def attainSet {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) : Set X :=
  {x | ∃ hx : x ∈ Prod.fst '' D, ∃ (y : Y) (h : (x, y) ∈ D),
    f ⟨(x, y), h⟩ = partialInf D f ⟨x, hx⟩}

end BertsekasShreve.AnalyticSelection
