import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Proof of Theorem 3.2, pp. 214–215: along every possible demand path, the base stock policy
incurs no larger one-period expected cost than any feasible policy in every period:
`G_i(y*_i) ≤ G_i(y_i)`. -/
theorem pathwise_G_dominance {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar) (hfeas : M.OrderFeasible)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.G k (M.orderSeq (M.baseStock ybar x₁) d k) ≤ M.G k (M.orderSeq Ŷ d k) := by sorry

end VeinottBaseStock
