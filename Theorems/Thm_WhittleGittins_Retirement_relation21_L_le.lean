import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (21) (p. 148): for every active project `i`, `F̂ ≥ Lᵢ F̂`, with equality if
`M ≤ Mᵢ` and `M₍ᵢ₎ ≤ Mᵢ` (i.e. `Mᵢ` is maximal among the indices of the active projects). -/
theorem relation21_L_le {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) (i : Fin N) (hi : 0 < s i) :
    LFhat B i x s M ≤ Fhat B x s M ∧
      (M ≤ index B i (x i) (s i) →
        (∀ j, j ≠ i → 0 < s j → index B j (x j) (s j) ≤ index B i (x i) (s i)) →
        LFhat B i x s M = Fhat B x s M) := by sorry

end WhittleGittins.Retirement

