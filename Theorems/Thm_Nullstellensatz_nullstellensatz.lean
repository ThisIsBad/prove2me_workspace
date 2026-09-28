import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem nullstellensatz {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (p : MvPolynomial (Fin n) k)
    (hp : ∀ a : Fin n → K, (∀ f ∈ J, aeval a f = 0) → aeval a p = 0) :
    ∃ r : ℕ, p ^ r ∈ J := by sorry

end Nullstellensatz
