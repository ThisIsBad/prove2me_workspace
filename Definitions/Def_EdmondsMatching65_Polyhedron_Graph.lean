import Mathlib

namespace EdmondsMatching65.Polyhedron

/-- A finite graph in the sense of Edmonds (1965), §1–§2, pp. 125–126: nodes `V`, edges `E`, and for
each edge the unordered pair of nodes it meets. Parallel edges are allowed (the contracted graphs
`Gᵢ` of Theorem (M) have them); loops are excluded. Finiteness is supplied by `[Fintype V]
[Fintype E]` at every use. A simple graph is the case `Function.Injective G.ends`. -/
structure Graph (V E : Type*) where
  /-- the unordered pair of end nodes of an edge -/
  ends : E → Sym2 V
  /-- no edge is a loop: its two ends are different nodes -/
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A *matching* in `G` (§1, p. 125): a set of edges no two of which meet the same node. -/
def IsMatching (G : Graph V E) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : V, v ∈ G.ends e → v ∉ G.ends f

/-- The incidence (0–1) vector of a set of edges `M`: `x e = 1` exactly when `e ∈ M`. -/
def incidence (M : Finset E) : E → ℝ :=
  fun e => if e ∈ M then 1 else 0

/-- A *maximum* matching for real edge weights `c` (§1, p. 125: a maximum-weight-sum matching):
a matching whose weight-sum `∑_{e ∈ M} c e` is at least that of every matching of `G`. -/
def IsMaximumMatching (G : Graph V E) (c : E → ℝ) (M : Finset E) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset E, IsMatching G M' → ∑ e ∈ M', c e ≤ ∑ e ∈ M, c e

end EdmondsMatching65.Polyhedron
