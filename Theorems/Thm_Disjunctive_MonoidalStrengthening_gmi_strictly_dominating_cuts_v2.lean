import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic


namespace Disjunctive.MonoidalStrengthening

/-- Theorem 11.26 (Balas, *Disjunctive Programming*, Springer 2018, §11.9.1, p. 187), the goal
theorem of the mission. Consider the simplex-tableau row `y = a_0 - Σ_j a_j x_j` of a basic
variable `y` that is a `0`-`1` variable (integer, with the bounds `0 ≤ y ≤ 1` of the LP
relaxation, which give the lower bounds `b_1 = a_0 - 1`, `b_2 = -a_0` of the two terms of the
split disjunction `y ≤ 0 ∨ y ≥ 1` used by the book's Lopsided-cut derivation), with
`0 < a_0 < 1`, the nonbasic variables `x ≥ 0`, and `x_j` integer for `j ∈ J₁`. Then every such
`x` satisfies both `α⁺x ≥ 1` and `α⁻x ≥ 1`, with `α⁺`, `α⁻` given by (11.55)/(11.56).

Correction w.r.t. the retired version: the retired statement kept only the disjunction
`y ≤ 0 ∨ y ≥ 1` on the real number `y`, dropping integrality and the bounds `0 ≤ y ≤ 1` of the
basic variable; hypothesis `hy` now says `y ∈ {0,1}`. -/
theorem gmi_strictly_dominating_cuts_v2 {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hy : a0 - ∑ j, a j * x j = 0 ∨ a0 - ∑ j, a j * x j = 1) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by sorry

end Disjunctive.MonoidalStrengthening

