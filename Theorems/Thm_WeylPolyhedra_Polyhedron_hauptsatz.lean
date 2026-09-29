import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §1, p. 291, Satz 1 (Hauptsatz): let `S` be a finite non-degenerate point
system in `ℝⁿ`. Every point `x` satisfying all extreme support inequalities of `S`
(`α ⬝ᵥ x ≥ 0` for every extreme support `α` of `S`) is a nonnegative linear combination of the
points of `S`. -/
theorem hauptsatz {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) (x : Fin n → ℝ)
    (hx : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ x) :
    Shared.Representable S x := by sorry

end WeylPolyhedra.Polyhedron

