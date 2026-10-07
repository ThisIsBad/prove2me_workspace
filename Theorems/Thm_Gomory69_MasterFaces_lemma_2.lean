import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), LEMMA 2, p. 472. -/
theorem lemma_2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀) (g : N) :
    ∃ t : N → ℕ, GroupSolution N g₀ t ∧
      dot π (castSolution t) = π₀ ∧ 0 < t g := by sorry

end Gomory69.MasterFaces

