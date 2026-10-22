import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Lemma 4.1, p. 666. -/
theorem lemma_4_1 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    (∃ e ∈ I.E, x e = 1) ∨
    (∃ w ∈ I.W, (degree (support I.E x) w : ℤ) ≤ I.B w + 1) := by sorry
end BoundedDegreeST.PlusOne

