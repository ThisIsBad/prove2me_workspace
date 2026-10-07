import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open Filter Topology

namespace KingmanSubadditive.Ulam

/-- **The Stirling step (2.4.8)** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), §2.4, proof of Theorem 8, p. 896). Let `0 < α < b < ∞`. If
`2α + (b − α) log (b − α) − α log α − b log b < 0`, then `P{l(π) ≥ b n^½} → 0` as `n → ∞`, where
`π` is uniform on `𝒮_n`.

**Formalization Note** The paper calls the free parameter `β`; it is `b` here because `β` is also
the constant of Theorem 8. The paper obtains this from (2.4.7) with `k ~ α n^½`, `r ~ β n^½`; the
statement is the conclusion, for every admissible pair `(α, b)`. -/
theorem eq_2_4_8 (α b : ℝ) (hα : 0 < α) (hαb : α < b) (h : stirlingExponent α b < 0) :
    Tendsto (fun n : ℕ => unifProb n (fun σ => b * Real.sqrt n ≤ (lis σ : ℝ))) atTop (𝓝 0) := by sorry

end KingmanSubadditive.Ulam

