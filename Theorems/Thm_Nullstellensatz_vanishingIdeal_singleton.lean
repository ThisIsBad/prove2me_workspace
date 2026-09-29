import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem vanishingIdeal_singleton {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (a : Fin n → K) :
    vanishingIdeal {a} = pointIdeal a ∧ (pointIdeal a).IsMaximal := by sorry

end Nullstellensatz
