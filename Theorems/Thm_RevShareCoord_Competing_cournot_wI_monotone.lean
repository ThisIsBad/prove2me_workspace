import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

/-- **Sec. 4.1.2, `w^I` increases with competition (p. 19).** Let `0 < c < 1` and
`w^I(β, n) = c + β(n − 1)(1 − c)/(2 + 2β(n − 1))`.
1. For every `n ≥ 2`, `w^I` is strictly increasing in `β ∈ [0, 1)`.
2. For every `β ∈ (0, 1)`, `w^I` is strictly increasing in the number of retailers `n ≥ 1`. -/
theorem cournot_wI_monotone (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ n : ℕ, 2 ≤ n → StrictMonoOn (fun β => cournotWI β n c) (Set.Ico 0 1)) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m k : ℕ, 1 ≤ m → m < k →
        cournotWI β m c < cournotWI β k c := by sorry

end RevShareCoord.Competing

