import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Theorem 4(a), p. 549. For the `n`-period model (`n = 2, 3, ⋯`) there exists an optimal
`(s, S)` policy whose first-period rule `(s_n, S_n)` satisfies
`s̲ ≤ s_n ≤ s̄ ≤ S̲ ≤ S_n ≤ S̄`. Optimality is against every admissible (history-dependent)
policy and for every initial level `x`. -/
theorem theorem4a_optimal_sS_within_bounds (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
      sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
      sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
      SLow G ≤ Sn ∧ Sn ≤ SHigh G K α := by sorry

end VeinottWagnerSS.Bounds

