import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Claim 5.8, p. 669: if `x` is feasible, `(𝓛, T_U, T_W)` is as in
Lemma 5.3 and `S ∈ 𝓛` has `r` members (its children in the forest of `𝓛`
and the supernodes inside `S` but in no child), then `x(D(S)) = r − 1`, where
`D(S)` is the set of support edges joining two different members of `S`. -/
theorem claim_5_8 {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hfeas : Feasible E A B U W F x)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (S : Finset V) (hS : S ∈ L) :
    BoundedDegreeST.PlusOne.edgeSum x (crossing E F x L S) = ((members F L S).card : ℝ) - 1 := by sorry

end BoundedDegreeST.LowerUpper

