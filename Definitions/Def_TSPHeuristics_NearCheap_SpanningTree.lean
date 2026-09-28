import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

open Classical

namespace TSPHeuristics.NearCheap

/-- The length of an undirected edge `{i, j}`: `(d i j + d j i) / 2`, which is `d i j` for a
symmetric distance (symmetrized so that it is well defined on unordered pairs). -/
noncomputable def edgeLen {n : ℕ} (d : Fin n → Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => (d i j + d j i) / 2, fun i j => by ring⟩

/-- The length of a graph `M` on the nodes: the sum of the lengths of its edges. For a spanning
tree (`M.IsTree`) this is the length of the tree; TREE (p. 573) is its minimum over trees. -/
noncomputable def treeWeight {n : ℕ} (d : Fin n → Fin n → ℝ) (M : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ M.edgeFinset, edgeLen d e

end TSPHeuristics.NearCheap
