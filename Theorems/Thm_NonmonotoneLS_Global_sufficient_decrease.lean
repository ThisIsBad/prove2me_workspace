import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eqs. (2.8)–(2.9) (p. 1047): along a run with `∇f(x_k) d_k ≤ 0` for every `k`, if (2.4)–(2.5)
hold with constants `c₁, c₂ > 0` for all `k ≥ K` and `∇f` is `L`-Lipschitz (`L > 0`) on `𝓛`
(Wolfe) or on `𝓛̄` (Armijo), then `f(x_{k+1}) ≤ C_k - β ‖∇f(x_k)‖²` for all `k ≥ K`, with
`β = min{δμc₁/ρ, 2δ(1-δ)c₁²/(Lρc₂²), δ(1-σ)c₁²/(Lc₂²)}`. -/
theorem sufficient_decrease {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (K : ℕ)
    (hdir : ∀ k, K ≤ k →
      ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
        ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzHyp p r f x d L) :
    ∀ k, K ≤ k →
      f (x (k + 1)) ≤ Shared.costC f x η k -
        min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / ((L : ℝ) * p.ρ * c₂ ^ 2)))
            (p.δ * (1 - p.σ) * c₁ ^ 2 / ((L : ℝ) * c₂ ^ 2)) *
          ‖gradient f (x k)‖ ^ 2 := by sorry

end NonmonotoneLS.Global

