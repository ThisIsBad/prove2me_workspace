import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter

namespace NonmonotoneLS.RLinear

/-- Eq. (3.6) (p. 1050), i.e. (2.8) with `β` of (2.9): along a run whose directions satisfy
(2.4)–(2.5) with constants `c₁, c₂ > 0` at every `k`, whose steps satisfy `α_k ≤ μ`, and for which
`∇f` is `L`-Lipschitz (`L > 0`) on `𝓛̄`, `f(x_{k+1}) ≤ C_k - β ‖∇f(x_k)‖²` for every `k`. -/
theorem sufficient_decrease {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, f (x (k + 1)) ≤ Shared.costC f x η k - beta p c₁ c₂ L * ‖gradient f (x k)‖ ^ 2 := by sorry

end NonmonotoneLS.RLinear

