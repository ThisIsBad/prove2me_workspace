import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1780, the labeling process: with non-negative arc lengths, every run of the labeling
process from the initial labels is finite — there is no infinite sequence of improving replacements. -/
theorem labeling_terminates {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) :
    ¬ ∃ f : ℕ → V → WithTop ℝ, f 0 = initLabel S ∧ ∀ i, RelaxStep N l (f i) (f (i + 1)) := by sorry

end FordFulkerson58.ArcChain

