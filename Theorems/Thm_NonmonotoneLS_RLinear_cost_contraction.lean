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

/-- Eq. (3.8) (p. 1050): if `f` is strongly convex in the sense of (3.1) with constant `γ`,
`x*` minimizes `f`, `η_max < 1`, the directions satisfy (2.4)–(2.5) with constants `c₁, c₂ > 0` at
every `k`, the steps satisfy `α_k ≤ μ`, and `∇f` is `L`-Lipschitz (`L > 0`) on `𝓛̄`, then
`C_{k+1} - f(x*) ≤ θ (C_k - f(x*))` for every `k`, where `θ = 1 - βb₂(1 - η_max)`,
`b₂ = 1/(β + γb²)`, `β` is given by (2.9) and `b = 1 + μc₂L`. -/
theorem cost_contraction {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, Shared.costC f x η (k + 1) - f xstar ≤
      theta p c₁ c₂ L γ * (Shared.costC f x η k - f xstar) := by sorry

end NonmonotoneLS.RLinear

