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

/-- Theorem 3.1 (p. 1049), with the direction assumption required at every `k` (repair (b)):
if `f` is strongly convex in the sense of (3.1), `x*` minimizes `f`, the directions of the run
satisfy (2.4)–(2.5) for every `k`, the steps satisfy `α_k ≤ μ` for all `k`, `η_max < 1`, and `∇f`
is Lipschitz continuous on bounded sets, then there is `θ ∈ (0, 1)` with
`f(x_k) - f(x*) ≤ θ^k (f(x_0) - f(x*))` for each `k`. -/
theorem r_linear_convergence {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdir : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (hLip : ∀ S : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded S →
      ∃ L : ℝ≥0, LipschitzOnWith L (gradient f) S) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ k, f (x k) - f xstar ≤ θ ^ k * (f (x 0) - f xstar) := by sorry

end NonmonotoneLS.RLinear

