import Mathlib

namespace ChvatalPolytopes.SeriesParallel

/-- "Delete `u` and identify its neighbors `v`, `w`" (Chvátal 1975, p. 151, proof of Theorem 7.1,
Case 4). The vertex set of the new graph is `V − {u, w}`; the vertex `v` stands for the merged
vertex `v ≡ w`. Two distinct vertices `a, b` of `V − {u, w}` are adjacent iff they are adjacent in
`G`, or one of them is `v` and the other is adjacent to `w` in `G`. (Parallel edges created by the
identification are merged and no loops arise, as the paper's graphs are simple.) -/
def deleteIdentify {V : Type*} (G : SimpleGraph V) (u v w : V) :
    SimpleGraph {x : V // x ≠ u ∧ x ≠ w} :=
  SimpleGraph.fromRel fun a b => G.Adj a.1 b.1 ∨ (a.1 = v ∧ G.Adj w b.1)

end ChvatalPolytopes.SeriesParallel
