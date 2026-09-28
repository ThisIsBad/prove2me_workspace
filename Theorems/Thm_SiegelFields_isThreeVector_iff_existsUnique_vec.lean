import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem isThreeVector_iff_existsUnique_vec (V : Matrix (Fin 2) (Fin 2) ℂ) :
    IsThreeVector V ↔ ∃! v : Fin 3 → ℝ, V = vecToMatrix v := by sorry
end SiegelFields
