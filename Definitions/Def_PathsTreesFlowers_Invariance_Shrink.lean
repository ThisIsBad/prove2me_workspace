import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The vertex of the shrunken graph to which the vertex `v` of `G` is sent: its part
`P.part v` of the partition `P`. -/
def partOf (P : Finpartition (Finset.univ : Finset V)) (v : V) : {U : Finset V // U ∈ P.parts} :=
  ⟨P.part v, P.part_mem.2 (Finset.mem_univ v)⟩

/-- The edges of `G` that survive shrinking the parts of `P`: those whose two end-points lie in
different parts. -/
abbrev ShrinkE (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) : Type :=
  {e : E // ¬ ((G.ends e).map (partOf P)).IsDiag}

/-- *Shrinking* (4.9–4.11, pp. 456–457) every part of the partition `P` of the vertices of `G` at
once. The vertices of `shrink G P` are the parts of `P` (a part with more than one vertex is a
pseudovertex, and the part is its complete expansion); its edges are the edges of `G` joining two
different parts, which keep their identity; an edge's end-points are the parts containing its
end-points in `G`. Edges with both end-points in one part disappear. Shrinking a single vertex set
`U` is the case where every other part is a singleton. -/
def shrink (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) :
    EdmondsMatching65.Polyhedron.Graph {U : Finset V // U ∈ P.parts} (ShrinkE G P) where
  ends e := (G.ends e.1).map (partOf P)
  loopless e := e.2

/-- `M/P = M ∩ (G/P)` (4.10, p. 457): the edges of `M` that survive in the shrunken graph. -/
def shrinkMatching (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) (M : Finset E) : Finset (ShrinkE G P) :=
  M.subtype _

/-- *Odd-circuit sets* (4.10, 4.11, 4.14, pp. 457–458): the complete expansions of pseudovertices
obtained by successively shrinking arbitrary odd circuits. The same induction as `IsBlossomSet`
without any condition on a matching. -/
inductive IsOddCircuitSet (G : EdmondsMatching65.Polyhedron.Graph V E) : Finset V → Prop
  | singleton (v : V) : IsOddCircuitSet G {v}
  | circuit (k : ℕ) (hk : 1 ≤ k) (U : Fin (2 * k + 1) → Finset V) (e : Fin (2 * k + 1) → E)
      (hU : ∀ i, IsOddCircuitSet G (U i))
      (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
      (hends : ∀ i, ∃ a ∈ U i, ∃ b ∈ U (i + 1), G.ends (e i) = s(a, b)) :
      IsOddCircuitSet G (Finset.univ.biUnion U)

end PathsTreesFlowers.Invariance
