import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem conj_vecToMatrix_eq_rotationOf (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (v : Fin 3 → ℝ) :
    U * vecToMatrix v * Uᴴ = vecToMatrix (rotationOf U *ᵥ v) := by sorry
end SiegelFields
