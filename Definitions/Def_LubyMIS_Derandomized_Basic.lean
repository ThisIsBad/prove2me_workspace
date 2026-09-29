import Mathlib

namespace LubyMIS.Derandomized

open Finset

/-- The neighbourhood `N(W) = {i ∈ V′ : ∃ j ∈ W, (i, j) ∈ E′}` of a vertex set `W` in the current
graph `H = G′` (Luby 1986, §3.1, p. 1038). -/
def nbhd {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V) :
    Finset V :=
  Finset.univ.filter (fun i => ∃ j ∈ W, H.Adj i j)

open Classical in
/-- The number of edges eliminated by one execution of the loop body that selects `I′`: the edges of
`H` with at least one endpoint in `Y = I′ ∪ N(I′)`. The induced subgraph on `V′ − Y` keeps exactly the
other edges, so this is `Y_k − Y_{k+1}` (§3.1, p. 1039; §3.4, p. 1040). -/
noncomputable def eliminated {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (I' : Finset V) : ℕ :=
  (H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ I' ∪ nbhd H I')).card

/-- `sum(i) = ∑_{j ∈ adj(i)} 1 / d(j)` (§3.4, p. 1041). The page defines it only for `d(i) ≥ 1`; at
`d(i) = 0` this is the empty sum `0`. -/
noncomputable def sumInv {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) : ℝ :=
  ∑ j ∈ H.neighborFinset i, 1 / (H.degree j : ℝ)

/-- Algorithm B's select step (§3.3, p. 1040) for the coin values `c` (`X = {i : c i = true}`,
`I′` starting at `X`): `i ∈ X` survives iff every neighbour `j ∈ X` has `d(j) < d(i)`. -/
def selectB {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (c : V → Bool) :
    Finset V :=
  Finset.univ.filter (fun i => c i = true ∧ ∀ j, H.Adj i j → c j = true → H.degree j < H.degree i)

end LubyMIS.Derandomized
