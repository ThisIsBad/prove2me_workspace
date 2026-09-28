import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Proofs of Theorems 3.1 (p. 211) and 3.2 (p. 215): under (3b), along every possible demand
path, once the base stock policy orders up to `ȳ_k` (because `q_k(x*_k) ≤ ȳ_k`) it orders up to
`ȳ_i` in every later period `i ≥ k`. -/
theorem base_stock_level_absorbing {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3b : M.H3b ybar)
    (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) (k : ℕ)
    (hk : M.q k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ≤ coeVec (ybar k)) :
    ∀ i, k ≤ i → M.orderSeq (M.baseStock ybar x₁) d i = ybar i := by sorry

end VeinottBaseStock
