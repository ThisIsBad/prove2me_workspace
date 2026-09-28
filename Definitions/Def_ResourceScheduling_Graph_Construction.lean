import Mathlib
import Definitions.Def_ResourceScheduling_Graph_ResDot11
import Definitions.Def_ResourceScheduling_Graph_GraphPartition

/-!
# The graph-to-schedule construction

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 15: given a graph `G` with vertex set `V` and edge
set `E`, one job `J_j` per vertex `j`, and for each vertex pair `{j, k} ∉ E` (with `j ≠ k`) a
resource `R_{j,k}` of size 1 with `r_{{j,k},j} = r_{{j,k},k} = 1` and `r_{{j,k},i} = 0`
otherwise.
-/

namespace ResourceScheduling.Graph

/-- The non-adjacent vertex pairs `{j, k}`, `j ≠ k`, each listed once as `(j, k)` with `j < k`,
in lexicographic order. They index the resources of the construction. -/
def nonEdgeList {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : List (Fin N × Fin N) :=
  (List.finRange N).flatMap fun j =>
    ((List.finRange N).filter fun k => decide (j < k ∧ ¬ G.Adj j k)).map fun k => (j, k)

/-- The construction of p. 15: jobs are the vertices of `G`; resource `h` is the `h`-th
non-adjacent pair `{j, k}` of `nonEdgeList G`, of size 1, required (amount 1) by `J_j` and `J_k`
only. The threshold is `y`. -/
def construct {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (y : ℕ) : ResDot11Data where
  n := N
  l := (nonEdgeList G).length
  r h i := if i = ((nonEdgeList G).get h).1 ∨ i = ((nonEdgeList G).get h).2 then 1 else 0
  r_le := by
    intro h i
    split <;> omega
  y := y

/-- The reduction applied to a graph instance with `|V| = 3t`: the construction with threshold
`y = t`. -/
def reduce (d : GraphData) : ResDot11Data :=
  construct d.G d.t

end ResourceScheduling.Graph
