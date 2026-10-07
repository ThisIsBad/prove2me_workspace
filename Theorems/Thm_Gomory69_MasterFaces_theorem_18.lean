import Mathlib
import Definitions.Def_Gomory69_MasterFaces_BasicFeasible

namespace Gomory69.MasterFaces

/-- Gomory (1969), THEOREM 18, pp. 481–483. -/
theorem theorem_18 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (hg₀ : g₀ ≠ 0) (π : MasterIndex G → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) :
    IsFace (masterSupport G) g₀ π π₀ ↔ IsSystem13Basic g₀ π₀ π := by sorry

end Gomory69.MasterFaces

