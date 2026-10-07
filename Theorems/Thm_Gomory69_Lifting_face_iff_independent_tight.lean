import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Lifting

theorem face_iff_independent_tight {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Nontrivial G]
    (g₀ : G) (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) :
    IsFace G g₀ π π₀ ↔
      (∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t) ∧
        ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
          (∀ i, s i ∈ T G g₀ ∧ π ⬝ᵥ castVec (s i) = π₀) ∧
            LinearIndependent ℝ (fun i => castVec (s i)) := by sorry

end Gomory69.Lifting

