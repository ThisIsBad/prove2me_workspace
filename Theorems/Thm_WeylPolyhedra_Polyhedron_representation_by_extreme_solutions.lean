import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3 II, p. 298 (proof of Satz 8 b)): let `S ⊆ ℝⁿ` be a finite non-degenerate
system of inequalities `a ⬝ᵥ ξ ≥ 0`. Every solution `π ∈ (S)` is a nonnegative linear
combination `π = l α + m β + ⋯` of finitely many extreme solutions `α, β, ⋯` of `S`. -/
theorem representation_by_extreme_solutions {n : ℕ} (S : Finset (Fin n → ℝ))
    (hS : Shared.NonDegenerate S) (π : Fin n → ℝ) (hπ : π ∈ solutionRegion S) :
    ∃ E : Finset (Fin n → ℝ), (∀ e ∈ E, IsExtremeSolution S e) ∧
      ∃ l : (Fin n → ℝ) → ℝ, (∀ e ∈ E, 0 ≤ l e) ∧ π = ∑ e ∈ E, l e • e := by sorry

end WeylPolyhedra.Polyhedron

