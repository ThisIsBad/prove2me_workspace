import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- Gomory (1969), THEOREM 17, pp. 480–481; `π(0) = 0` by extension. -/
theorem theorem_17 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (hg₀ : g₀ ≠ 0) (π : MasterIndex G → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace (masterSupport G) g₀ π π₀) :
    (∀ g : MasterIndex G,
      extendZero π (g : G) + extendZero π (g₀ - (g : G)) = π₀) ∧
    (∀ g h : MasterIndex G,
      extendZero π ((g : G) + (h : G)) ≤ π g + π h) ∧
    extendZero π g₀ = π₀ := by sorry

end Gomory69.MasterFaces

