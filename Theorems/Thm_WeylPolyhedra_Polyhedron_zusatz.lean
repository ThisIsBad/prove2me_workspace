import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §2, pp. 294–295, Zusatz (to the Hauptsatz): for a finite non-degenerate point
system `S ⊆ ℝⁿ`, `S` has no extreme support (case b) of the Hauptsatz) if and only if `0` is
representable by `S` with every coefficient strictly positive:
`0 = ∑_{s ∈ S} c_s s` with `c_s > 0` for all `s ∈ S`. -/
theorem zusatz {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) :
    (¬ ∃ α : Fin n → ℝ, Shared.IsExtremeSupport S α) ↔
      ∃ c : (Fin n → ℝ) → ℝ, (∀ s ∈ S, 0 < c s) ∧ (0 : Fin n → ℝ) = ∑ s ∈ S, c s • s := by sorry

end WeylPolyhedra.Polyhedron

