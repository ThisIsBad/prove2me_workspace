import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem conj_eq_conj_iff (U W : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V → U * V * Uᴴ = W * V * Wᴴ) ↔
      W = U ∨ W = -U := by sorry
end SiegelFields
