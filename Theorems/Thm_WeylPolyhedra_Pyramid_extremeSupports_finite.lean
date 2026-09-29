import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §1, p. 291: a finite non-degenerate point system `S ⊆ ℝⁿ` has only finitely
many extreme supports, counted up to positive scaling (positive multiples of a normal give the
same half-space, p. 291): there is a finite set `F` of extreme supports of `S` such that every
extreme support of `S` is a positive multiple of a member of `F`. -/
theorem extremeSupports_finite {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) :
    ∃ F : Finset (Fin n → ℝ), (∀ β ∈ F, Shared.IsExtremeSupport S β) ∧
      ∀ α, Shared.IsExtremeSupport S α → ∃ β ∈ F, ∃ c : ℝ, 0 < c ∧ α = c • β := by sorry

end WeylPolyhedra.Pyramid

