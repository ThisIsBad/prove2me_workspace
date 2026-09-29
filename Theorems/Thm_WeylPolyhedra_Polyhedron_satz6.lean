import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3, p. 297, Satz 6: let `S ⊆ ℝⁿ` be a finite non-degenerate system of
inequalities `a ⬝ᵥ ξ ≥ 0` (non-degeneracy is the standing hypothesis of Satz 4, which Satz 6
restates). Then `p` lies in the region `(Σ)` of the dual system — `α ⬝ᵥ p ≥ 0` for every
extreme solution `α` of `S` — if and only if `p ⬝ᵥ ξ ≥ 0` for every `ξ ∈ (S)`. -/
theorem satz6 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) (p : Fin n → ℝ) :
    p ∈ dualRegion S ↔ ∀ ξ ∈ solutionRegion S, 0 ≤ p ⬝ᵥ ξ := by sorry

end WeylPolyhedra.Polyhedron

