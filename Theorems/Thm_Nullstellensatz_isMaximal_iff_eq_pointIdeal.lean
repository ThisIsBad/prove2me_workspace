import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem isMaximal_iff_eq_pointIdeal {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (m : Ideal (MvPolynomial (Fin n) K)) :
    m.IsMaximal ↔ ∃ a : Fin n → K, m = pointIdeal a := by sorry

end Nullstellensatz
