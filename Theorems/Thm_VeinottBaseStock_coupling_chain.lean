import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- (3.1), p. 214: let `x*, y*` be the base stock trajectory and `x, y` the trajectory of an
arbitrary feasible policy from the same `x_1` along the same possible demand path. For every
period `k` before the first period `T` with `q_T(x*_T) ≤ ȳ_T`,
`ȳ_k < y*_k = w_k(x*_k) ≤ w_k(x_k) ≤ y_k`. -/
theorem coupling_chain {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar) (hfeas : M.OrderFeasible)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j)
    (k : ℕ)
    (hbefore : ∀ j ≤ k, ¬ M.q j (M.stateSeq (M.baseStock ybar x₁) x₁ d j) ≤ coeVec (ybar j)) :
    ybar k < M.orderSeq (M.baseStock ybar x₁) d k ∧
      M.orderSeq (M.baseStock ybar x₁) d k =
        M.w ybar k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ∧
      M.w ybar k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ≤
        M.w ybar k (M.stateSeq Ŷ x₁ d k) ∧
      M.w ybar k (M.stateSeq Ŷ x₁ d k) ≤ M.orderSeq Ŷ d k := by sorry

end VeinottBaseStock
