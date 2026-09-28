import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem unitary_conj_threeVector (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : IsThreeVector V) :
    IsThreeVector (U * V * Uᴴ) ∧ (U * V * Uᴴ).det = V.det := by sorry
end SiegelFields
