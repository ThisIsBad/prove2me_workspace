import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Theorem 11.26 (Balas §11.9.1, p. 187), the goal theorem of this mission: for a tableau row
`y = a_0 - Σ_j a_j x_j` (`0 < a_0 < 1`), `x ≥ 0`, integer on `J₁`, both `α⁺x ≥ 1` and `α⁻x ≥ 1`
are valid cuts, i.e. hold for every `x` on either branch of the split disjunction `y ≤ 0 ∨ y ≥ 1`
from (11.50)/(11.51). -/
theorem gmi_strictly_dominating_cuts {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_disj : a0 - ∑ j, a j * x j ≤ 0 ∨ 1 ≤ a0 - ∑ j, a j * x j) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by sorry

end Disjunctive.MonoidalStrengthening

