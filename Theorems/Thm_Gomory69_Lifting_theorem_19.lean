import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Lifting

theorem theorem_19 {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    IsFace G g₀ (liftCoeff ψ π') π₀ := by sorry

end Gomory69.Lifting

