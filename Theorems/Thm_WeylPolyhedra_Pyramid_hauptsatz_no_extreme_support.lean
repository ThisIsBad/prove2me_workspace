import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §1, p. 291 (case b) of the Hauptsatz, proved in §2 b), pp. 293–294): if a finite
non-degenerate point system `S ⊆ ℝⁿ` has no extreme support at all, then every point of `ℝⁿ` is
a nonnegative linear combination of the points of `S`. -/
theorem hauptsatz_no_extreme_support {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hnone : ∀ α : Fin n → ℝ, ¬ Shared.IsExtremeSupport S α) (x : Fin n → ℝ) :
    Shared.Representable S x := by sorry

end WeylPolyhedra.Pyramid

