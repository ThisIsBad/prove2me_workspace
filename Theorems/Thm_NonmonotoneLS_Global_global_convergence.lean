import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Theorem 2.2 (p. 1047). Let `f` be continuously differentiable and bounded from below, and let
`(x_k, d_k, α_k, η_k)` be a run of the NLSA with `∇f(x_k) d_k ≤ 0` for every `k`, satisfying the
direction assumption (2.4)–(2.5), where `∇f` is Lipschitz on `𝓛` if the Wolfe conditions are used
and on `𝓛̄` if the Armijo conditions are used. Then
(2.6) `liminf_k ‖∇f(x_k)‖ = 0` (stated as: for every `ε > 0`, `‖∇f(x_k)‖ < ε` for infinitely
many `k`); and if `η_max < 1`, (2.7) `∇f(x_k) → 0` and every limit of a convergent subsequence
of `(x_k)` is a stationary point. -/
theorem global_convergence {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (hdir : DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (p.ηmax < 1 → Tendsto (fun k => gradient f (x k)) atTop (𝓝 0)) ∧
      (p.ηmax < 1 → ∀ xstar : EuclideanSpace ℝ (Fin n),
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 xstar)) →
          gradient f xstar = 0) := by sorry

end NonmonotoneLS.Global

