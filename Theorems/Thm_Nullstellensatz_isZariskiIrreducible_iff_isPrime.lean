import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem isZariskiIrreducible_iff_isPrime {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (W : Set (Fin n → K)) (hW : IsAlgebraicSet W) :
    IsZariskiIrreducible W ↔ (vanishingIdeal W).IsPrime := by sorry

end Nullstellensatz
