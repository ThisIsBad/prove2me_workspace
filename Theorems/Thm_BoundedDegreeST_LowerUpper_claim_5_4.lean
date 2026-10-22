import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.4, p. 668, in the setting of §5.1: `x` is a basic
feasible solution, `F` is not a spanning tree, `(𝓛, T_U, T_W)` is as in
Lemma 5.3, `T = T_U ∪ T_W`, and (contradiction hypotheses) there is no 1-edge
and no `v ∈ U ∪ W` with `deg_{E*}(v) = 2`. A special supernode (excess exactly
one) contains exactly one active vertex `v`, and `v ∈ T` with
`deg_{E*}(v) = 3`. -/
theorem claim_5_4
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (C : Finset V) (hC : IsSpecialSupernode E F x (TU ∪ TW) C) :
    ∃ v ∈ C, Active E x v ∧ (∀ w ∈ C, Active E x w → w = v) ∧
      v ∈ TU ∪ TW ∧ degree (support E x) v = 3 := by sorry

end BoundedDegreeST.LowerUpper

