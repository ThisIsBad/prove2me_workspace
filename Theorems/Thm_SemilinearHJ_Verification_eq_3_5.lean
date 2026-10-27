import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem eq_3_5 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ X, ∀ u ∈ vectorSpan ℝ X, r / n * l1 u - r * psiNorm X Ψ ≤ ham X Ψ r x u := by sorry

end SemilinearHJ.Verification

