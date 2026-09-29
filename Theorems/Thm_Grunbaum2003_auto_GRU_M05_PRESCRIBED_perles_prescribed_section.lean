import Definitions.Def_auto_GRU_M05_PRESCRIBED_IsDPolytope
import Definitions.Def_auto_GRU_M05_PRESCRIBED_faceCount
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option autoImplicit false

namespace Grunbaum2003

theorem auto_GRU_M05_PRESCRIBED_perles_prescribed_section (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : auto_GRU_M05_PRESCRIBED_IsDPolytope P)
    (hfacets : (if d = 0 then 0 else auto_GRU_M05_PRESCRIBED_faceCount P (d - 1)) ≤ k + 1)
    (v : Fin (k + 1) → (Fin k → ℝ)) (hv : AffineIndependent ℝ v)
    (p : Fin k → ℝ) (hp : p ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ L : AffineSubspace ℝ (Fin k → ℝ),
      p ∈ L ∧ Module.finrank ℝ L.direction = d ∧
      ∃ A : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ),
        Function.Injective A ∧ Set.range A = (L : Set (Fin k → ℝ)) ∧
          A '' P = convexHull ℝ (Set.range v) ∩ (L : Set (Fin k → ℝ)) := by sorry

end Grunbaum2003
