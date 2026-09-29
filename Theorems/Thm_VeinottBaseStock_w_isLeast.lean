import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- §3, p. 212: under (3a) and (3c), for every `x ∈ X_i` the set
`Y_i ∩ {y | y ≥ q_i(x), y ≥ ȳ_i}` has the least element `w_i(x)`, and `w_i(x) = ȳ_i` whenever
`q_i(x) ≤ ȳ_i`. -/
theorem w_isLeast {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (hM : M.Standing) (h3a : M.H3a ybar) (h3c : M.H3c) (hfeas : M.OrderFeasible)
    (k : ℕ) (x : Fin n → ℝ) (hx : x ∈ M.X k) :
    IsLeast (M.orderSet ybar k x) (M.w ybar k x) ∧
      (M.q k x ≤ coeVec (ybar k) → M.w ybar k x = ybar k) := by sorry

end VeinottBaseStock
