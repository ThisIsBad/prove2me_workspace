import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP
import Definitions.Def_PolyhedralSOC_Sandwich_Conditions

namespace PolyhedralSOC.Sandwich

/-- **Proposition 4.1** (Ben-Tal & Nemirovski, *On Polyhedral Approximations of the
Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF p. 11)).
Assume that (CQP), with `m ≥ 1` conic constraints, is
(i) strictly feasible: there exist `x̄` and `r > 0` with `Ax̄ ≥ b`,
`‖A_ℓ x̄ − b_ℓ‖₂ ≤ [c_ℓᵀx̄ − d_ℓ] − r` for all `ℓ`;
(ii) semibounded: every feasible `x` of (CQP) has `c_ℓᵀx − d_ℓ ≤ R` for all `ℓ`.
Then for every `ε > 0` with `γ(ε) = Rε/r < 1`,
`(14)  γ(ε) x̄ + (1 − γ(ε)) Feas(CQP_ε) ⊂ Feas(CQP) ⊂ Feas(CQP_ε)`.
The left-hand side is the image of `Feas(CQP_ε)` under `y ↦ γ(ε) x̄ + (1 − γ(ε)) y`.
Corrections of the printed statement: in (i) the page prints `c_ℓᵀx` for `c_ℓᵀx̄` (the proof
uses `x̄`); `m ≥ 1` is added, since for `m = 0` hypothesis (ii) is vacuous, `R` may be
negative, and the left inclusion fails. -/
theorem feasible_set_sandwich {n k₀ m : ℕ} (P : CQP n k₀ m) (hm : 0 < m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (R : ℝ) (hii : IsSemibounded P R)
    (ε : ℝ) (hε : 0 < ε) (hγ : R * ε / r < 1) :
    (fun y => (R * ε / r) • xbar + (1 - R * ε / r) • y) '' feasRelaxed P ε ⊆ feas P ∧
      feas P ⊆ feasRelaxed P ε := by sorry

end PolyhedralSOC.Sandwich

