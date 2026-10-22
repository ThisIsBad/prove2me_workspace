import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Lemma 5.6, p. 669, as a counting statement, in the setting of
§5.1 (see Claim 5.4), with `T = T_U ∪ T_W`. For every `S ∈ 𝓛`, the
`∑_{v ∈ S} deg_{E*}(v)` tokens of the vertices of `S` cover two tokens for every
vertex of `T ∩ S`, two for every member of `𝓛` strictly inside `S`, and at
least three for `S`; and the root gets exactly three only if `S` is a special
set or `S = V`. -/
theorem lemma_5_6
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) :
    3 ≤ surplus E x L (TU ∪ TW) S ∧
      (surplus E x L (TU ∪ TW) S = 3 →
        IsSpecialSet E x L (TU ∪ TW) S ∨ S = Finset.univ) := by sorry

end BoundedDegreeST.LowerUpper

