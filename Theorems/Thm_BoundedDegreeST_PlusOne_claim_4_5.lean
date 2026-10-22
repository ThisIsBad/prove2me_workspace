import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Claim 4.5, p. 667. -/
theorem claim_4_5 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (v : V)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F)
    (hbasis : DefinesBasis I.E I.B I.W I.F x L T)
    (hnoone : ∀ e ∈ support I.E x, x e ≠ 1)
    (hnosmall : ∀ w ∈ I.W, (degree (support I.E x) w : ℤ) > I.B w + 1)
    (hactive : 0 < degree (support I.E x) v)
    (hone : excessTokens (support I.E x) T v = 1) :
    (v ∉ T ∧ degree (support I.E x) v = 1) ∨
    (v ∈ T ∧ degree (support I.E x) v = 3 ∧ I.B v = 1) := by sorry
end BoundedDegreeST.PlusOne

