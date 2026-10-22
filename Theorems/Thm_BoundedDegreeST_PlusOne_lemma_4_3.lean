import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Lemma 4.3, p. 666. -/
theorem lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    ∃ (L : Finset (Finset V)) (T : Finset V),
      DefinesBasis I.E I.B I.W I.F x L T := by sorry
end BoundedDegreeST.PlusOne

