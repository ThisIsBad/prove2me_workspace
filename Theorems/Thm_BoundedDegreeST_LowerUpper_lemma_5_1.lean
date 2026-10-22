import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Lemma 5.1, p. 668: a basic feasible solution `x*` of
LP-MBDCT(G, 𝓐, 𝓑, U, W, F) with support `E*` has an edge `e` with `x*_e = 1`,
or a vertex `v ∈ U ∪ W` with `deg_{E*}(v) = 2`. The hypothesis that `F` is not
a spanning tree is implicit in the paper (Step 1 has not returned). -/
theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V) (x : Sym2 V → ℝ)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F) :
    (∃ e ∈ E, x e = 1) ∨ (∃ v ∈ U ∪ W, degree (support E x) v = 2) := by sorry

end BoundedDegreeST.LowerUpper

