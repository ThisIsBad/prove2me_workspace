import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, proof of (1), p. 114: if `i ∈ S` lies in the first cycle `Sʲ` that meets the coalition
`S` (every member of `S` has stage `≥ j`), then `i` already gets, from his cyclic successor,
the highest payoff available to him from the items of `S`. -/
theorem best_in_coalition_of_first_stage {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) (S : Finset N) (i : N) (hi : i ∈ S)
    (hfirst : ∀ k ∈ S, P.stage i ≤ P.stage k) :
    ∀ k ∈ S, A i k ≤ A i (P.next i) := by sorry

end ShapleyScarf.TopTrading

