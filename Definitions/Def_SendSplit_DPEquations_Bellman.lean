import Mathlib
import Definitions.Def_BertsekasSPGraph

namespace SendSplit.DPEquations

/-- A simple circuit of the graph `G`: a list of `m ≥ 2` distinct nodes `[v₀, …, v_{m-1}]`
such that `(v₀, v₁), …, (v_{m-2}, v_{m-1}), (v_{m-1}, v₀)` are all arcs of `G`. -/
def IsSimpleCircuit {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)
    (l : List V) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧ List.IsChain (fun x y => (x, y) ∈ G.arcs) (l ++ l.take 1)

/-- The cost of traversing the circuit `[v₀, …, v_{m-1}]`: the length of the closed walk
`(v₀, …, v_{m-1}, v₀)`. -/
def circuitLength {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)
    (l : List V) : ℝ :=
  BertsekasWalkLength G (l ++ l.take 1)

/-- A `+∞`-or-real-valued solution of Bellman's equations for minimum-cost chains to the
node `t = G.t` (Eq. (2)′, p. 642): `C_t = 0` and, for every node `k ≠ t`,
`C_k = min_{(k,j) ∈ arcs} [a_kj + C_j]`, the minimum over no arcs being `+∞`. -/
def IsBellmanSolution {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)
    (C : V → EReal) : Prop :=
  (∀ k, C k ≠ ⊥) ∧ C G.t = 0 ∧
    ∀ k, k ≠ G.t →
      C k = (Finset.univ.filter (fun j => (k, j) ∈ G.arcs)).inf
        (fun j => ((G.length k j : ℝ) : EReal) + C j)

end SendSplit.DPEquations
