import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem su2_double_cover_so3 :
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf (U * W) = rotationOf U * rotationOf W) ∧
    (∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∃ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, rotationOf U = R) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U = rotationOf W ↔ W = U ∨ W = -U) := by sorry
end SiegelFields
