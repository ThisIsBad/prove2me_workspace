import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem rank_D_sub_one {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
      (∀ i, s i ∈ T G g₀ ∧ liftCoeff ψ π' ⬝ᵥ castVec (s i) = π₀) ∧
        LinearIndependent ℝ (fun i => castVec (s i)) := by sorry

end Gomory69.Lifting

