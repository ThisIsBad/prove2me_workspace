import Mathlib
import Definitions.Def_RobustSDP_FullPert_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- Theorem 3.1, p. 36, as a set identity. Full perturbations `𝒟 = ℝ^{p×q}` (`⊤`), `ρ > 0`,
the standing hypothesis `‖D‖ < ρ⁻¹` of §3.1, `F₀, …, F_m` symmetric, `q ≥ 1`, and `L ≠ 0`
(added: the printed statement fails for `L = 0`). Then `x` lies in the robust feasible set
`𝒳_ρ` (2) iff there is `τ` making the block matrix of the SDP (10) positive semidefinite.
Since (4) and (10) share the objective `cᵀx`, this is the content of "the RSDP (4) and a
corresponding solution `x` can be computed by solving the SDP (10)". -/
theorem theorem_3_1 {m n p q : ℕ} (hq : 0 < q)
    (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hFs : ∀ i, (Fs i).IsSymm)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (hL : L ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (hD : ‖D‖ < ρ⁻¹)
    (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs Rs L D ⊤ ρ ↔
      ∃ τ : ℝ, (sdpLMI (affineMap Fs x) (affineMap Rs x) L D ρ τ).PosSemidef := by sorry

end RobustSDP.FullPert

