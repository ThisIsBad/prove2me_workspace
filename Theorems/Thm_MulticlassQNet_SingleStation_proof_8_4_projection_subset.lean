import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra

namespace MulticlassQNet.SingleStation

/-- Proof of Theorem 8.4 (p. 38), first half ("In Theorem 4.4 we have shown that P2' ⊆ P1"):
the projection of P2 on the `n_i` coordinates is contained in P1. -/
theorem proof_8_4_projection_subset {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} ⊆ P1 lam mu := by sorry

end MulticlassQNet.SingleStation

