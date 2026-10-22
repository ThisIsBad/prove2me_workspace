import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem cutSum_compatible {V : Type*} [Fintype V] [DecidableEq V]
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ) :
    Compatible (atomPartition Rs Cs) (cutSum Rs Cs d) := by sorry

end FriezeKannan.PseudoReg

