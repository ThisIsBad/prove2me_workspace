import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem weak_nullstellensatz_system {K : Type*} [Field K] [IsAlgClosed K] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) K) :
    (¬ ∃ a : Fin n → K, ∀ i, eval a (f i) = 0) ↔
      ∃ g : Fin m → MvPolynomial (Fin n) K, ∑ i, g i * f i = 1 := by sorry

end Nullstellensatz
