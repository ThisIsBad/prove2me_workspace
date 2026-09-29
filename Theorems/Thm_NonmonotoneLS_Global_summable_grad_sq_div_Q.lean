import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eq. (2.14) (p. 1048): under the hypotheses of Theorem 2.2 (with `∇f(x_k) d_k ≤ 0` for every
`k`), `∑_{k=0}^∞ ‖∇f(x_k)‖² / Q_{k+1} < ∞`. -/
theorem summable_grad_sq_div_Q {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (hdir : DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    Summable (fun k => ‖gradient f (x k)‖ ^ 2 / Shared.costQ η (k + 1)) := by sorry

end NonmonotoneLS.Global

