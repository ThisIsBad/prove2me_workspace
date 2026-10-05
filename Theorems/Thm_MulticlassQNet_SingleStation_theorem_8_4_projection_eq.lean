import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra

namespace MulticlassQNet.SingleStation

/-- Theorem 8.4 (p. 38): the polyhedron P2, defined by (69)–(71) and nonnegativity in the
`O(n²)` variables `(n_i, I_ij)`, projected on the `n_i` coordinates, is exactly P1. -/
theorem theorem_8_4_projection_eq {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} = P1 lam mu := by sorry

end MulticlassQNet.SingleStation

