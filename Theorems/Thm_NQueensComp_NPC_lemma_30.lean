import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 30, p. 834: within each of `G¹_c, G²_c, G³_c` (columns `Cᵢ`, rows `Rᵢ`), the
difference-diagonals `α − β` with `α ∈ Cᵢ, β ∈ Rᵢ` are all distinct, and so are the sum-diagonals
`α + β`. -/
theorem lemma_30 (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    ∀ G ∈ [G1 cs j, G2 cs j, G3 cs j],
      (∀ p ∈ G.C ×ˢ G.R, ∀ p' ∈ G.C ×ˢ G.R, diffDiag p = diffDiag p' → p = p') ∧
      (∀ p ∈ G.C ×ˢ G.R, ∀ p' ∈ G.C ×ˢ G.R, sumDiag p = sumDiag p' → p = p') := by sorry

end NQueensComp.NPC

