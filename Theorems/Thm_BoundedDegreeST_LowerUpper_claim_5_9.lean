import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.9, p. 669, in the setting of §5.1 (see Claim 5.4), with
`T = T_U ∪ T_W`: if `S ∈ 𝓛`, `S ≠ V`, `S` has exactly three members, all
three special (each a special supernode or a special set), and `|D(S)| ≥ 3`,
then `S` is a special set (Definition 5.5). -/
theorem claim_5_9
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) (hSV : S ≠ Finset.univ)
    (hthree : (members F L S).card = 3)
    (hspecial : ∀ R ∈ members F L S, IsSpecialMember E F x L (TU ∪ TW) R)
    (hD : 3 ≤ (crossing E F x L S).card) :
    IsSpecialSet E x L (TU ∪ TW) S := by sorry

end BoundedDegreeST.LowerUpper

