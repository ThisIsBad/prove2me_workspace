import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3 III, p. 299, Satz 9: let `S ⊆ ℝⁿ` be a finite non-degenerate system of
inequalities `a ⬝ᵥ ξ ≥ 0` whose region `(S)` contains an inner point `ξ⁰`
(`a ⬝ᵥ ξ⁰ > 0` for every `a ∈ S`). Then the dual system `Σ` is non-degenerate: the only `p`
with `α ⬝ᵥ p = 0` for every extreme solution `α` of `S` is `p = 0`. -/
theorem satz9 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ p : Fin n → ℝ, (∀ α : Fin n → ℝ, IsExtremeSolution S α → α ⬝ᵥ p = 0) → p = 0 := by sorry

end WeylPolyhedra.Polyhedron

