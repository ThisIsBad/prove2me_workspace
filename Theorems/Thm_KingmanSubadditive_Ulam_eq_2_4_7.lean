import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- **(2.4.7)** (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4,
proof of Theorem 8, p. 896). For `π` uniform on `𝒮_n`, every positive integer `k` and every
`r ≥ k`, `P{l(π) ≥ r} ≤ (n choose k)[k! (r choose k)]⁻¹`.

**Formalization Note** `k` is positive, as in the paper ("let `k` be any positive integer");
`r ≥ k` makes `(r choose k) ≥ 1`, so the right side has no division by zero. The bound is exact
and holds for every `n`. -/
theorem eq_2_4_7 (n k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    unifProb n (fun σ => r ≤ lis σ) ≤
      (n.choose k : ℝ) / ((Nat.factorial k : ℝ) * (r.choose k : ℝ)) := by sorry

end KingmanSubadditive.Ulam

