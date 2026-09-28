import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem weak_nullstellensatz {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (hJ : J ≠ ⊤) :
    ∃ a : Fin n → K, ∀ f ∈ J, aeval a f = 0 := by sorry

end Nullstellensatz
