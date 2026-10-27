import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem observation_4_1 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) :
    ∀ x ∈ X, ∀ ρ : ℝ, 0 < ρ →
      (∃ y ∈ X, l1 (y - x) ≤ ρ ∧ srcVal X Ψ r X0 x = srcVal X Ψ r X0 y + minCost X Ψ r y x) ∧
      ∀ y ∈ X, l1 (y - x) ≤ ρ → srcVal X Ψ r X0 x ≤ srcVal X Ψ r X0 y + minCost X Ψ r y x := by sorry

end SemilinearHJ.Verification

