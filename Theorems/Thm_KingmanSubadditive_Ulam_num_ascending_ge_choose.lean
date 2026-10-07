import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4, proof of
Theorem 8, p. 896.) If `l(π) ≥ k`, there is an ascending sequence of length `l(π)`, and each of its
subsequences of length `k` is ascending, so `ν ≥ (l(π) choose k)`, where `ν` is the number of
ascending sequences of length `k` in `π`. The statement is deterministic: it holds for every
permutation `σ ∈ 𝒮_n`. -/
theorem num_ascending_ge_choose {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ lis σ) :
    (lis σ).choose k ≤ numAscending k σ := by sorry

end KingmanSubadditive.Ulam

