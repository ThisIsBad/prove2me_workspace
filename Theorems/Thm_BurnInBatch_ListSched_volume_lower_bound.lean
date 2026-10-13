import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proof of Proposition 1, p. 772: total job processing volume divided by `mB`
is a lower bound for the optimum batch makespan. -/
theorem volume_lower_bound {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (hn : 0 < n) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) :
    (∑ j : Fin n, p j) / ((m : ℝ) * (B : ℝ)) ≤
      CmaxStar p B m Finset.univ := by sorry

end BurnInBatch.ListSched

