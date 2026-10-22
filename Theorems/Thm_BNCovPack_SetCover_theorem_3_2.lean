import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_BNCovPack_SetCover_FracScheme

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Theorem 3.2** (Buchbinder–Naor 2009, p. 5), covering half, on a set-cover instance
(`a ∈ {0,1}`): if every arriving constraint (element `e`) has at most `ℓ` non-zero coefficients
(`|𝒮_e| ≤ ℓ`), then for every `B > 0` the Section 3 scheme with `n` replaced by `ℓ`
(i) produces a feasible fractional cover of the arrived elements, and
(ii) has primal cost at most `2 ln(1 + ℓ)` times the cost of any fractional cover of them.
The paper writes `O(log ℓ)`; the proof of Theorem 3.1 with `n → ℓ` yields `2 ln(1 + ℓ)`. -/
theorem theorem_3_2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (σ : List E) (hfreq : ∀ e ∈ σ, (inst.elemSets e).card ≤ ℓ)
    (hσ : ∀ e ∈ σ, (inst.elemSets e).Nonempty) :
    (∀ e ∈ σ, 1 ≤ elementWeight inst (fracRun inst B ℓ σ).w e) ∧
    ∀ w'' : T → ℝ, (∀ s, 0 ≤ w'' s) → (∀ e ∈ σ, 1 ≤ elementWeight inst w'' e) →
      ∑ s, inst.c s * (fracRun inst B ℓ σ).w s
        ≤ 2 * Real.log (1 + (ℓ : ℝ)) * ∑ s, inst.c s * w'' s := by sorry

end BNCovPack.SetCover

