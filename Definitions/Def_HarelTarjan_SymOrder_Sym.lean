import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree

namespace HarelTarjan.SymOrder

/-- The symmetric-order (in-order) sort key of a path `s`: each turn is written `0` (left) or `2`
(right), and the marker `1` ("the vertex itself") is appended. Comparing keys lexicographically
places, for every vertex, its whole left subtree first, then the vertex, then its whole right
subtree: this is symmetric (in-order) traversal order. -/
def key (s : List Bool) : List ℕ :=
  s.map (fun b => if b then 2 else 0) ++ [1]

/-- The symmetric-order number `sym(v)` of a vertex `v` of the complete binary tree of depth `d`
(Harel–Tarjan, §3, p. 341, Fig. 1): the vertices are numbered from `1` to `n` in symmetric order,
so `sym(v)` is the number of vertices `u` that come no later than `v` in symmetric order, i.e. whose
key is lexicographically `≤` the key of `v` (`≤` on `List ℕ` is the lexicographic order). -/
def sym {d : ℕ} (v : Vertex d) : ℕ :=
  (Finset.univ.filter (fun u : Vertex d => key u.1 ≤ key v.1)).card

end HarelTarjan.SymOrder
