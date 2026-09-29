import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §2, p. 295, Satz 2 (Verschärfung des Hauptsatzes): let `S ⊆ ℝⁿ` be a finite
non-degenerate point system. Every point `x` that satisfies all extreme support inequalities of
`S` is a nonnegative linear combination of at most `n` points of `S`. -/
theorem hauptsatz_at_most_n {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (x : Fin n → ℝ) (hx : ∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → 0 ≤ α ⬝ᵥ x) :
    ∃ T : Finset (Fin n → ℝ), T ⊆ S ∧ T.card ≤ n ∧ Shared.Representable T x := by sorry

end WeylPolyhedra.Pyramid

