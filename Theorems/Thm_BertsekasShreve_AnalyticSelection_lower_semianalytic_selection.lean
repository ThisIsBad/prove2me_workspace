import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_BertsekasShreve_AnalyticSelection_LowerSemianalytic

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Proposition 7.50** (pp. 184–185). Let `X`, `Y` be Borel spaces, `D ⊆ X × Y` analytic and
`f : D → R*` lower semianalytic, with `f*(x) = inf_{y ∈ D_x} f(x, y)` on `proj_X(D)`.
(a) For every `ε > 0` there is an analytically measurable `φ : proj_X(D) → Y` with graph in `D`
and `f(x, φ x) ≤ f*(x) + ε` where `f*(x) > -∞`, `f(x, φ x) ≤ -1/ε` where `f*(x) = -∞`.
(b) The set `I` where the infimum is attained is universally measurable, and for every `ε > 0`
there is a universally measurable `φ : proj_X(D) → Y` with graph in `D`, `f(x, φ x) = f*(x)` on
`I`, and the bounds of (a) off `I`. -/
theorem lower_semianalytic_selection {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal) (hf : IsLowerSemianalytic D f) :
    -- (a)
    (∀ ε : ℝ, 0 < ε →
      ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
        IsAnalyticallyMeasurableFun (Prod.fst '' D) φ ∧
        ∀ x : Prod.fst '' D,
          (partialInf D f x ≠ ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
          (partialInf D f x = ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal))) ∧
    -- (b)
    (IsUniversallyMeasurable (attainSet D f) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
          IsUniversallyMeasurableFun (Prod.fst '' D) φ ∧
          ∀ x : Prod.fst '' D,
            ((x : X) ∈ attainSet D f → f ⟨((x : X), φ x), hφ x⟩ = partialInf D f x) ∧
            ((x : X) ∉ attainSet D f → partialInf D f x ≠ ⊥ →
              f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
            ((x : X) ∉ attainSet D f → partialInf D f x = ⊥ →
              f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal))) := by sorry

end BertsekasShreve.AnalyticSelection

