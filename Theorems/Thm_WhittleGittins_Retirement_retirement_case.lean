import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Retirement case of the proof of Theorem 1 (p. 148): if `maxⱼ Mⱼ ≤ M` (over the active
projects) then `F̂(x, s, M) = M`, and `M ≥ Lᵢ F̂` for every active `i`, so `F̂` satisfies (16)
with the retirement option. -/
theorem retirement_case {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ)
    (hM : ∀ j, 0 < s j → index B j (x j) (s j) ≤ M) :
    Fhat B x s M = M ∧ ∀ i, 0 < s i → LFhat B i x s M ≤ M := by sorry

end WhittleGittins.Retirement

