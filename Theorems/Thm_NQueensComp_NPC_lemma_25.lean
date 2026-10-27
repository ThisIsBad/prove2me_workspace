import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 25, p. 831: for a gadget `G = ⟨n, C, R, D⁻, {}⟩` and `δ ≥ 0`, a set of queens `Q` is a
solution to `G` iff `Q + (δ, 0)` is a solution to `G ⊕ δ`. -/
theorem lemma_25 (G : Inst4) (hG : G.Dp = ∅) (δ : ℕ) (Q : Finset Queen) :
    G.IsSol Q ↔ (G.shift δ).IsSol (shiftSet Q (δ, 0)) := by sorry

end NQueensComp.NPC

