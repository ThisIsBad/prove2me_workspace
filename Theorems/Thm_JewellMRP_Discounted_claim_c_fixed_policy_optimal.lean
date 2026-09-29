import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (c), p. 946: if the policy-improvement step reproduces the policy `d`, then no
stationary policy has a higher return than `d` in any state. -/
theorem claim_c_fixed_policy_optimal {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) {d : S → A} {v : S → ℝ}
    (hv : SolvesEval M α d v) (hfix : IsImprovement M α d v d)
    (e : S → A) (w : S → ℝ) (hw : SolvesEval M α e w) : ∀ i, w i ≤ v i := by sorry

end JewellMRP.Discounted
