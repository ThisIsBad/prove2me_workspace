import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- The full-perturbation case of `𝓑`, p. 37 (paragraph after Theorem 3.2): when `𝒟 = ℝ^{p×q}`
(with `p, q ≥ 1`), a triple `(S, T, G)` lies in the (corrected) scaling set `𝓑` iff `G = 0` and
`S = τ I_p`, `T = τ I_q` for one scalar `τ`; if moreover `S ⪰ 0`, then `τ ≥ 0`. -/
theorem full_scaling_set {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ) :
    ((S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) ↔
        ∃ τ : ℝ, S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧ T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧
          G = 0) ∧
      (S.PosSemidef → (S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) →
        ∃ τ : ℝ, 0 ≤ τ ∧ S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧
          T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧ G = 0) := by sorry

end RobustSDP.Structured
