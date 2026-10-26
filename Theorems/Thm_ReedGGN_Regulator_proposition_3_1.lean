import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proposition 3.1 (p. 9), with the added hypothesis `B({0}) < 1` (`μ {0} < 1`), without which
the statement is false (`B` = unit mass at `0`, `a = 0`, `x ≡ 1` has no solution).
There is a map `φ^a_B : D[0,∞) → D[0,∞)` such that `φ^a_B(x)` solves (3.1), every càdlàg
solution agrees with it on `[0, ∞)`, it is Lipschitz in the supremum metric on every
`[0, T]` (constant depending on `T` only), and it is measurable for the Kolmogorov
σ-algebra (= the Borel σ-algebra of the Skorohod `J₁` topology). -/
theorem proposition_3_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ {0} < 1) (a : ℝ) :
    ∃ Φ : Dpath → Dpath,
      (∀ x : Dpath, SolvesRegulator μ a x.path (Φ x).path) ∧
      (∀ (x z : Dpath), SolvesRegulator μ a x.path z.path →
        Set.EqOn z.path (Φ x).path (Set.Ici 0)) ∧
      (∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, ∀ x₁ x₂ : Dpath,
        supNorm T ((Φ x₁).path - (Φ x₂).path) ≤ C * supNorm T (x₁.path - x₂.path)) ∧
      Measurable Φ := by sorry

end ReedGGN.Regulator

