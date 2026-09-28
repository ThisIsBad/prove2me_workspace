import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Complexity
import Definitions.Def_cubic_p3_partition_models

/-!
# PARTITION INTO TRIANGLES and PARTITION INTO PATHS OF LENGTH 2

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 15, proofs of Theorems 2 and 3, citing Garey &
Johnson (1979), problems GT11 and GT13. An instance is a graph `G = (V, E)` with `|V| = 3t`;
here `V = Fin (3 * t)`, so `|V| = 3t` is part of the instance.
-/

namespace ResourceScheduling.Graph

/-- An instance of the two graph partition problems: `t` and a graph on `3t` vertices with
decidable adjacency. -/
structure GraphData where
  t : ℕ
  G : SimpleGraph (Fin (3 * t))
  [decAdj : DecidableRel G.Adj]

attribute [instance] GraphData.decAdj

/-- Code of a graph instance: `t` in unary, then the `3t × 3t` adjacency matrix row by row,
`one` for an edge and `sep` for a non-edge. -/
def encGraph (d : GraphData) : List Letter :=
  unary d.t ++
    (List.finRange (3 * d.t)).flatMap fun i =>
      (List.finRange (3 * d.t)).map fun j => if d.G.Adj i j then Letter.one else Letter.sep

/-- PARTITION INTO TRIANGLES: `V` can be partitioned into `t` disjoint subsets, each containing
three pairwise adjacent vertices. The bijection `place` lists the three vertices of each block. -/
def PartitionIntoTriangles {t : ℕ} (G : SimpleGraph (Fin (3 * t))) : Prop :=
  ∃ place : Fin t × Fin 3 ≃ Fin (3 * t),
    ∀ (i : Fin t) (a b : Fin 3), a ≠ b → G.Adj (place (i, a)) (place (i, b))

/-- PARTITION INTO PATHS OF LENGTH 2: `V` can be partitioned into disjoint subsets of three
vertices, each containing at least two of its three possible edges (at most one nonadjacent
pair), i.e. `G` has a (not necessarily induced) `P₃`-factor. -/
def PartitionIntoPathsOfLength2 {t : ℕ} (G : SimpleGraph (Fin (3 * t))) : Prop :=
  Nonempty (CubicP3Partition.P3Factor G)

/-- The language of PARTITION INTO TRIANGLES. -/
def trianglesLang : CookPvsNP.Lang Letter :=
  codeLang (fun d : GraphData => PartitionIntoTriangles d.G) encGraph

/-- The language of PARTITION INTO PATHS OF LENGTH 2. -/
def pathsLang : CookPvsNP.Lang Letter :=
  codeLang (fun d : GraphData => PartitionIntoPathsOfLength2 d.G) encGraph

end ResourceScheduling.Graph
