import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Proof of Theorem 3.2, p. 214: since `q_i(x)` is nondecreasing in `x` where
`q_i(x) ≰ ȳ_i`, so is `w_i(x)`. -/
theorem w_monotone {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (hM : M.Standing) (h3a : M.H3a ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (hfeas : M.OrderFeasible) (k : ℕ) (x x' : Fin n → ℝ) (hx : x ∈ M.X k) (hx' : x' ∈ M.X k)
    (hle : x ≤ x') (hq : ¬ M.q k x ≤ coeVec (ybar k)) :
    M.w ybar k x ≤ M.w ybar k x' := by sorry

end VeinottBaseStock
