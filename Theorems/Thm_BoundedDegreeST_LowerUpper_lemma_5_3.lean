import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Lemma 5.3, p. 668: a basic feasible solution of
LP-MBDCT(G, 𝓐, 𝓑, U, W, F) is the unique solution of a linearly independent
system of tight rows given by `T_U ⊆ U`, `T_W ⊆ W` and a nonempty laminar
family `𝓛 ⊆ 𝓘(F)`, with `|E*| = |𝓛| + |T_U| + |T_W|`. The hypothesis that `F`
is not a spanning tree is implicit in the paper (Step 1 has not returned). -/
theorem lemma_5_3 {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V) (x : Sym2 V → ℝ)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F) :
    ∃ (TU TW : Finset V) (L : Finset (Finset V)),
      DefinesBasis E A B U W F x L TU TW := by sorry

end BoundedDegreeST.LowerUpper

