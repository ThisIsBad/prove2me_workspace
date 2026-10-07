import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-- Formula (9), p. 24: if job `k` is scheduled directly after job `j` (read: `B_k = B_j + δ`
with `δ ≥ 0`, and on every machine the operation of `j` ends before the operation of `k`
starts), the least admissible `δ` is `c_{jk} = max_{1 ≤ i ≤ m} {q_{j i} − q_{k,i−1}}`. -/
theorem formula_9_delay {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (j k : Fin n)
    (hjk : j ≠ k) :
    IsLeast {δ : ℤ | 0 ≤ δ ∧ ∀ r : Fin m, (cum p j (r.val + 1) : ℤ) ≤ δ + (cum p k r.val : ℤ)}
      (delay p hm j k) := by sorry

end SchedComplexity.NoWait

