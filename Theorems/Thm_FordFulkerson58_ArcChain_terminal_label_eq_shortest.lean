import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1780: when the labeling process (with non-negative lengths) stops, every label is the length
of a shortest chain from `S` to its node, and the smallest label on `T` is the length of a shortest
chain from `S` to `T`. -/
theorem terminal_label_eq_shortest {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S T : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab) :
    (∀ v, lab v = shortestChainLength N l S v) ∧ T.inf lab = shortestChainLengthTo N l S T := by sorry

end FordFulkerson58.ArcChain

