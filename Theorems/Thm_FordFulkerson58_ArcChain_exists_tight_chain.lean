import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1780, the trace-back: at the end of the labeling process (non-negative lengths), every node
`v ∉ S` with a finite label has a tight arc `e` into it (`lab u + l e = lab v`), and some chain from a
node of `S` to `v` consists of tight arcs and has length `lab v`. -/
theorem exists_tight_chain {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab)
    (v : V) (hv : lab v ≠ ⊤) :
    (v ∉ S → ∃ (e : E) (u : V), Traverses N e u v ∧ lab u + (l e : WithTop ℝ) = lab v) ∧
    ∃ u ∈ S, ∃ (p : List E) (vs : List V), IsChainWalk N u v p vs ∧
      (∀ (i : ℕ) (h : i < p.length), ∃ x y : V, vs[i]? = some x ∧ vs[i + 1]? = some y ∧
        lab y = lab x + (l p[i] : WithTop ℝ)) ∧
      ((chainLength l p.toFinset : ℝ) : WithTop ℝ) = lab v := by sorry

end FordFulkerson58.ArcChain

