import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem vanishingIdeal_zeroSet_eq_radical {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) :
    vanishingIdeal (zeroSet J) = J.radical := by sorry

end Nullstellensatz
