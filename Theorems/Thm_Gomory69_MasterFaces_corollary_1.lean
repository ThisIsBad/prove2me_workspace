import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), COROLLARY 1, p. 473. -/
theorem corollary_1 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀)
    (g₁ g₂ g : N) (hsum : (g : G) = (g₁ : G) + (g₂ : G)) :
    π g ≤ π g₁ + π g₂ := by sorry

end Gomory69.MasterFaces

