import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Lemma 4.6, p. 667, as the numerical token-distribution bound. -/
theorem lemma_4_6 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F)
    (hbasis : DefinesBasis I.E I.B I.W I.F x L T)
    (hnoone : ∀ e ∈ support I.E x, x e ≠ 1)
    (hnosmall : ∀ w ∈ I.W, (degree (support I.E x) w : ℤ) > I.B w + 1)
    (hroot : S ∈ L) :
    2 * (T ∩ S).card +
      2 * (L.filter (fun R => R ⊂ S)).card + 4 ≤
      ∑ v ∈ S, degree (support I.E x) v := by sorry
end BoundedDegreeST.PlusOne

