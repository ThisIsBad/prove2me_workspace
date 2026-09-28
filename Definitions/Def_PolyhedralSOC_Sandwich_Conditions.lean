import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP

open Matrix

namespace PolyhedralSOC.Sandwich

/-- Hypothesis (i) of Proposition 4.1 (Ben-Tal & Nemirovski, *On Polyhedral Approximations
of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF p. 11)):
`x̄` is a strictly feasible point of (CQP) with margin `r > 0`, i.e.
`Ax̄ ≥ b` and `‖A_ℓ x̄ − b_ℓ‖₂ ≤ [c_ℓᵀx̄ − d_ℓ] − r` for every `ℓ`.
(The page prints `c_ℓᵀx` without the bar on the right-hand side; the proof on the same page
uses `c_ℓᵀx̄ − d_ℓ − r`, which is what is formalized here.) -/
def IsStrictlyFeasible {n k₀ m : ℕ} (P : CQP n k₀ m) (xbar : Fin n → ℝ) (r : ℝ) : Prop :=
  0 < r ∧ (∀ i, P.b i ≤ (P.A *ᵥ xbar) i) ∧
    ∀ ℓ, eucNorm (P.Aℓ ℓ *ᵥ xbar - P.bℓ ℓ) ≤ (P.c ℓ ⬝ᵥ xbar - P.d ℓ) - r

/-- Hypothesis (ii) of Proposition 4.1 (Ben-Tal & Nemirovski 2001, p. 203 (PDF p. 11)):
(CQP) is "semibounded" with bound `R`, i.e. every feasible `x` of (CQP) satisfies
`c_ℓᵀx − d_ℓ ≤ R` for every `ℓ`. -/
def IsSemibounded {n k₀ m : ℕ} (P : CQP n k₀ m) (R : ℝ) : Prop :=
  ∀ x ∈ feas P, ∀ ℓ, P.c ℓ ⬝ᵥ x - P.d ℓ ≤ R

end PolyhedralSOC.Sandwich
