import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Corollary 2.3 (p. 1048). Suppose `η_max < 1`, `f` is continuously differentiable and bounded
from below, and `(x_k, d_k, α_k, η_k)` is a run of the NLSA with `∇f(x_k) d_k ≤ 0` for every `k`,
where `∇f` is Lipschitz on `𝓛` (Wolfe) or on `𝓛̄` (Armijo). Assume (2.4) for all sufficiently
large `k` and the growth condition (2.16) `‖d_k‖² ≤ τ₁ + τ₂ k` for each `k` (`τ₁ > 0`, `τ₂ ≥ 0`).
If `τ₂ ≠ 0` then `liminf ‖∇f(x_k)‖ = 0` (2.17); if `τ₂ = 0` then `‖∇f(x_k)‖ → 0` (2.18). -/
theorem corollary_growth {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η) (hηmax : p.ηmax < 1)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hdir : ∀ᶠ k in atTop, ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2)
    (τ₁ τ₂ : ℝ) (hτ₁ : 0 < τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgrowth : ∀ k : ℕ, ‖d k‖ ^ 2 ≤ τ₁ + τ₂ * k)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (τ₂ ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (τ₂ = 0 → Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0)) := by sorry

end NonmonotoneLS.Global

