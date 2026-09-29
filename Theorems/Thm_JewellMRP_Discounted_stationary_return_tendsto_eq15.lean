import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Eq. (15), p. 945: the `n`-step return of a stationary policy `d` converges, for every
choice of boundary rewards, to a solution of the equations (15) of `d`. -/
theorem stationary_return_tendsto_eq15 {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) (V0 : S → ℝ) :
    ∃ v : S → ℝ, SolvesEval M α d v ∧
      Tendsto (fun n => policyReturn M α (fun _ => d) V0 n) atTop (𝓝 v) := by sorry

end JewellMRP.Discounted
