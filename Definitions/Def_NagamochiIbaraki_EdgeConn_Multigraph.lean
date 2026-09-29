import Mathlib

namespace NagamochiIbaraki.EdgeConn

/-! Finite multigraphs (Nagamochi–Ibaraki 1992, p. 583 and §2, p. 584).

A graph `G = (V, E)` is encoded by a node type `V`, an edge type `E` and the map
`ends : E → Sym2 V` sending each edge to its unordered pair of end nodes. Parallel edges are
distinct elements of `E` with the same image; self-loops are excluded by the hypothesis
`∀ e, ¬ (ends e).IsDiag` carried by the theorems, and simplicity is `Function.Injective ends`.
An edge subset is a `Finset E`. -/

variable {V E : Type*}

/-- The simple graph on `V` recording which pairs of nodes are joined by at least one edge of
`F`. Reachability in `edgeGraph ends F` is connectivity by a path using edges of `F` only;
multiplicities play no role in reachability. -/
def edgeGraph (ends : E → Sym2 V) (F : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (ends '' (F : Set E))

/-- `(V, F)` is a forest (a multigraph without cycles): every edge of `F` is a bridge of `F`,
i.e. removing it from `F` disconnects its two end nodes. Two parallel edges form a cycle, so
neither of them is a bridge. -/
def IsForest [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) : Prop :=
  ∀ e ∈ F, ∀ u v : V, ends e = s(u, v) → ¬ (edgeGraph ends (F.erase e)).Reachable u v

/-- `(V, F)` is a maximal spanning forest in the spanning subgraph `(V, H)`: `F ⊆ H`, `F` is a
forest, and adding any further edge of `H` to `F` creates a cycle. The node set is all of `V`,
so every such forest is spanning. -/
def IsMaxSpanningForest [DecidableEq E] (ends : E → Sym2 V) (H F : Finset E) : Prop :=
  F ⊆ H ∧ IsForest ends F ∧ ∀ e ∈ H, e ∉ F → ¬ IsForest ends (insert e F)

/-- The degree of the node `v` in the spanning subgraph `(V, F)`: the number of edges of `F`
incident to `v`, parallel edges counted separately. -/
def degIn [DecidableEq V] (ends : E → Sym2 V) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e => v ∈ ends e)).card

end NagamochiIbaraki.EdgeConn
