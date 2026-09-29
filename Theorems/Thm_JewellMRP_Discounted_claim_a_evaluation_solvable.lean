import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (a), p. 946: for every `α > 0` and every stationary policy `d`, the
value-determination equations (15) have exactly one solution. -/
theorem claim_a_evaluation_solvable {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) : ∃! v : S → ℝ, SolvesEval M α d v := by sorry

end JewellMRP.Discounted
