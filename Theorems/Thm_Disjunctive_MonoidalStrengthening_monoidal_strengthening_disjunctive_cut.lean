import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Theorem 11.19 (Balas §11.8, p. 176, [24]): for the `q`-term disjunctive-cut situation with
per-term coefficients `a^h_j`, right-hand sides `a^h_0`, lower bounds `b^h_0 ≤ a^h_0` and
multipliers `θ_h ≥ 0`, every `x ≥ 0` satisfying `Σ_j a^h_j x_j ≥ b^h_0` for every `h` (the
background system (11.13)) and satisfying the disjunction `∨_h(Σ_j a^h_j x_j ≥ a^h_0)` also
satisfies the monoidally-strengthened cut `Σ_j α_j x_j ≥ α_0`, `α_j` given by `AlphaJStrengthened`
on `J₁` and `AlphaJUnstrengthened` elsewhere. The integrality of `x_j` for `j ∈ J₁` is (11.26)
and is what the monoid argument uses; without it the strengthened cut is invalid (`q = 2`,
`n = 1`, `J₁ = {0}`, `a¹ = 1.5`, `a¹₀ = 0.5`, `b¹ = -0.5`, `a² = -1.5`, `a²₀ = 0.5`,
`b² = -0.5`, `θ = (1,1)` gives the cut `x ≥ 1`, satisfied by no `x = 1/3` though `x = 1/3` meets
every other hypothesis). -/
theorem monoidal_strengthening_disjunctive_cut {q n : ℕ} [Nonempty (Fin q)]
    (acoef : Fin q → Fin n → ℝ) (a0 b0 theta : Fin q → ℝ) (J1 : Finset (Fin n))
    (hb0 : ∀ h, b0 h ≤ a0 h) (htheta : ∀ h, 0 ≤ theta h)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x)
    (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ h, b0 h ≤ ∑ j, acoef h j * x j)
    (hx_disj : ∃ h, a0 h ≤ ∑ j, acoef h j * x j) :
    Alpha0 theta a0 ≤
      ∑ j ∈ J1, AlphaJStrengthened theta a0 b0 acoef j * x j +
        ∑ j ∈ Finset.univ \ J1, AlphaJUnstrengthened theta acoef j * x j := by sorry

end Disjunctive.MonoidalStrengthening

