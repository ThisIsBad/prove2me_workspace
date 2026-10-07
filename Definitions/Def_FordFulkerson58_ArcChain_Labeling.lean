import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network

namespace FordFulkerson58.ArcChain

variable {V E ι : Type*}

/-- The length of a set of arcs `C` under the arc lengths `l`: `∑_{e ∈ C} l e`. -/
def chainLength (l : E → ℝ) (C : Finset E) : ℝ :=
  ∑ e ∈ C, l e

/-- The initial labels of the labeling process (§3, p. 1780): `0` on the source set `S`, `∞` (`⊤`)
elsewhere. -/
def initLabel [DecidableEq V] (S : Finset V) : V → WithTop ℝ :=
  fun v => if v ∈ S then 0 else ⊤

/-- One step of the labeling process (§3, p. 1780): an arc `e` traversable from `u` to `v` with
`lab u + l e < lab v` is found, and the label of `v` is replaced by `lab u + l e`. -/
def RelaxStep [DecidableEq V] (N : Network V E ι) (l : E → ℝ) (lab lab' : V → WithTop ℝ) : Prop :=
  ∃ (e : E) (u v : V), Traverses N e u v ∧ lab u + (l e : WithTop ℝ) < lab v ∧
    lab' = Function.update lab v (lab u + (l e : WithTop ℝ))

/-- A labeling is terminal when no arc can improve it: for every arc `e` traversable from `u` to `v`,
`lab v ≤ lab u + l e`. -/
def IsTerminal (N : Network V E ι) (l : E → ℝ) (lab : V → WithTop ℝ) : Prop :=
  ∀ (e : E) (u v : V), Traverses N e u v → lab v ≤ lab u + (l e : WithTop ℝ)

/-- The length of a shortest chain from the set `S` to the node `v`: the minimum of `chainLength l C`
over all chains `C` from `S` to `v`, and `⊤` (∞) if there is none. -/
noncomputable def shortestChainLength [Fintype E] [DecidableEq E] (N : Network V E ι) (l : E → ℝ) (S : Finset V)
    (v : V) : WithTop ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset E)).filter (fun C => IsChainFrom N S v C)).inf
    (fun C => ((chainLength l C : ℝ) : WithTop ℝ))

/-- The length of a shortest chain from the set `S` to the set `T`: the minimum of `chainLength l C`
over all chains `C` from `S` to some node of `T`, and `⊤` (∞) if there is none. -/
noncomputable def shortestChainLengthTo [Fintype E] [DecidableEq E] (N : Network V E ι) (l : E → ℝ)
    (S T : Finset V) : WithTop ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset E)).filter (fun C => ∃ t ∈ T, IsChainFrom N S t C)).inf
    (fun C => ((chainLength l C : ℝ) : WithTop ℝ))

end FordFulkerson58.ArcChain
