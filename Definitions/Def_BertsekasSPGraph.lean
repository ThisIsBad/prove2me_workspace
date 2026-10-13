import Mathlib

/-- The shortest path setting of Bertsekas, "Dynamic Programming and Optimal
Control", Vol. I, 3rd ed., Section 2.3: a finite directed graph with arc set
`arcs`, arc lengths `length`, an origin node `s` and a destination node `t`. -/
structure BertsekasSPGraph (V : Type) [Fintype V] [DecidableEq V] where
  arcs : Finset (V × V)
  length : V → V → ℝ
  s : V
  t : V
  hst : s ≠ t

/-- `BertsekasIsWalkFrom G a b l` says the list of nodes `l` is a path
(a forward walk) in the graph `G` from node `a` to node `b`: it is nonempty,
consecutive nodes are joined by arcs of `G`, it starts at `a` and ends at `b`. -/
def BertsekasIsWalkFrom {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (a b : V) (l : List V) : Prop :=
  l ≠ [] ∧ List.IsChain (fun x y => (x, y) ∈ G.arcs) l ∧
    l.head? = some a ∧ l.getLast? = some b

/-- The length of a walk, i.e. the sum of the lengths of its consecutive arcs. -/
def BertsekasWalkLength {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (l : List V) : ℝ :=
  ((l.zip l.tail).map fun p => G.length p.1 p.2).sum

/-- The shortest distance from `a` to `b` in `G`, as an extended real number:
the infimum of the lengths of all walks from `a` to `b` (`⊤` if none exists). -/
noncomputable def BertsekasShortestDistance {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (a b : V) : EReal :=
  ⨅ l : {l : List V // BertsekasIsWalkFrom G a b l}, (BertsekasWalkLength G l.1 : EReal)