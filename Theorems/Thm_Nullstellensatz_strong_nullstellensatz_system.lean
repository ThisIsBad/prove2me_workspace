import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem strong_nullstellensatz_system {K : Type*} [Field K] [IsAlgClosed K] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) K) (p : MvPolynomial (Fin n) K) :
    (∀ a : Fin n → K, (∀ i, eval a (f i) = 0) → eval a p = 0) ↔
      ∃ r : ℕ, ∃ g : Fin m → MvPolynomial (Fin n) K, p ^ r = ∑ i, g i * f i := by sorry

end Nullstellensatz
