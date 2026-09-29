import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (b), p. 946: if the policy-improvement step changes the policy `d` into `d' ≠ d`,
then the return of `d'` is at least that of `d` in every state and strictly greater in at
least one state. -/
theorem claim_b_strict_improvement {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) {d d' : S → A} {v v' : S → ℝ}
    (hv : SolvesEval M α d v) (hv' : SolvesEval M α d' v')
    (himp : IsImprovement M α d v d') (hne : d' ≠ d) :
    (∀ i, v i ≤ v' i) ∧ ∃ i, v i < v' i := by sorry

end JewellMRP.Discounted
