import Mathlib
import Definitions.Def_Gomory69_MasterFaces_BasicFeasible

namespace Gomory69.MasterFaces

/-- Gomory (1969), THEOREM 7, pp. 469–470. `N` is nonempty (`n′ ≥ 1`, p. 457): at
`N = ∅` the tight-row span is trivially full while no face exists. -/
theorem theorem_7 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (hNne : N.Nonempty) (g₀ : G) (π : N → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) :
    IsFace N g₀ π π₀ ↔ IsTBasicFeasible N g₀ π₀ π := by sorry

end Gomory69.MasterFaces

