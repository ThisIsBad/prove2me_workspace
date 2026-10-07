import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open scoped BigOperators

namespace KingmanSubadditive.Ulam

/-- The first moment of `ν` (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), §2.4, proof of Theorem 8, p. 896). Let `k` be a positive integer, let `π` be
uniform on `𝒮_n` and let `ν` be the number of sequences `i₁ < ⋯ < i_k ≤ n` with
`π(i₁) < ⋯ < π(i_k)`. Then `E(ν) = (n choose k)(k!)⁻¹`.

**Formalization Note** The expectation under the uniform law is the average over the `n!`
permutations of `Fin n`. -/
theorem expected_num_ascending (n k : ℕ) (hk : 0 < k) :
    (∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ)) / (Nat.factorial n : ℝ) =
      (n.choose k : ℝ) / (Nat.factorial k : ℝ) := by sorry

end KingmanSubadditive.Ulam

