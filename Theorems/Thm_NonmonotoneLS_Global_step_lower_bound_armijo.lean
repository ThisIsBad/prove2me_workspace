import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Lemma 2.1, Armijo case (p. 1046), Eq. (2.2): if `∇f(x) d ≤ 0`, `f(x) ≤ C`, `α` satisfies the
nonmonotone Armijo conditions at `(x, d, C)`, and, when `ρ α ≤ μ`,
`‖∇f(y) - ∇f(x)‖ ≤ L ‖y - x‖` for every `y` on the segment from `x` to `x + α ρ d`, then
`α ≥ min{μ/ρ, (2(1 - δ)/(L ρ)) |∇f(x) d| / ‖d‖²}`. -/
theorem step_lower_bound_armijo {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0) (hfC : f x ≤ C)
    (hstep : Shared.IsArmijoStep p f x d C α)
    (hLip : p.ρ * α ≤ p.μ → ∀ y ∈ segment ℝ x (x + (p.ρ * α) • d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖) :
    min (p.μ / p.ρ)
        (2 * (1 - p.δ) / (L * p.ρ) * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2)) ≤ α := by sorry

end NonmonotoneLS.Global

