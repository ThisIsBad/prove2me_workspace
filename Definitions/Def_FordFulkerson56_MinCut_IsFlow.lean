import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- The load of arc `e` under the chain-flow assignment `f : Finset E → ℝ`: the sum of the numbers of
all chain flows that contain `e`. -/
def load (f : Finset E → ℝ) (e : E) : ℝ :=
  ∑ C ∈ (Finset.univ : Finset (Finset E)).filter (fun C => e ∈ C), f C

/-- The value of a flow: the sum of the numbers of all its chain flows (p. 400). -/
def value (f : Finset E → ℝ) : ℝ :=
  ∑ C, f C

/-- A flow in the network `N` (Ford–Fulkerson, p. 399): a non-negative number `f C` on every set of
arcs `C`, nonzero only on chains joining the source and the sink, such that the load of every arc is
at most its capacity. -/
def IsFlow (N : Network V E) (f : Finset E → ℝ) : Prop :=
  (∀ C, 0 ≤ f C) ∧ (∀ C, f C ≠ 0 → IsChain N N.source N.sink C) ∧ ∀ e, load f e ≤ N.cap e

/-- Arc `e` is saturated by `f` when its load equals its capacity (p. 399). -/
def Saturated (N : Network V E) (f : Finset E → ℝ) (e : E) : Prop :=
  load f e = N.cap e

/-- A maximal flow: a flow whose value is at least the value of every flow. -/
def IsMaxFlow (N : Network V E) (f : Finset E → ℝ) : Prop :=
  IsFlow N f ∧ ∀ g, IsFlow N g → value g ≤ value f

end FordFulkerson56.MinCut
