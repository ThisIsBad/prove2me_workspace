import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Remark 1 (p. 942): under the hypotheses of Proposition 7, every run of (3.1) satisfies
`T⁻¹0 ⊂ H_n ∩ W_n` for each `n ≥ 0`. -/
theorem remark1_zeros_subset [StrictConvexSpace ℝ E] (hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, zeros T ⊆ halfH v y n ∩ halfW J x n := by sorry

end ProximalBanach.Hybrid
