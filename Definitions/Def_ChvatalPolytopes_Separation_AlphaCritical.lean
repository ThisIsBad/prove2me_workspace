import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Critical edge** (Chvátal 1975, p. 143): an edge `e` of `G` is *critical* if
`α(G − e) = α(G) + 1`, where `α = indepNum` is the stability number and `G − e` is `G` with the
edge `e` deleted. -/
def IsCriticalEdge {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ (G.deleteEdges {e}).indepNum = G.indepNum + 1

/-- The spanning subgraph `G* = (V, E*)` of `G` whose edges are the critical edges of `G`
(Chvátal 1975, p. 143, Theorem 4.2). -/
def criticalGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | IsCriticalEdge G e}

/-- **α-critical graph** (Chvátal 1975, p. 143): a graph all of whose edges are critical. -/
def IsAlphaCritical {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, IsCriticalEdge G e

end ChvatalPolytopes.Separation
