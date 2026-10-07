import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem liftedPath_minimal {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (g₀ : G)
    (π' : Plus H → ℝ) (π₀ : ℝ) (τ : Plus H → ℕ) (hτ : τ ∈ T H (ψ g₀))
    (hτπ : π' ⬝ᵥ castVec τ = π₀) (k : G) (hk : ψ k = 0) :
    ψ (closingElement ψ φ g₀ k τ) = 0 ∧
      liftedPath ψ φ g₀ k τ ∈ T G g₀ ∧
        liftCoeff ψ π' ⬝ᵥ castVec (liftedPath ψ φ g₀ k τ) = π₀ := by sorry

end Gomory69.Lifting

