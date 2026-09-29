import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- § The Optimal Policy with Discounting, p. 946: in the infinite-step discounted problem there
is a stationary policy `d` whose return `v` (the solution of (15)) is at least the limiting
return of every, possibly nonstationary, policy, from every state and for all boundary
rewards. -/
theorem exists_optimal_stationary {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ (d : S → A) (v : S → ℝ), SolvesEval M α d v ∧
      ∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
        Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v i := by sorry

end JewellMRP.Discounted
