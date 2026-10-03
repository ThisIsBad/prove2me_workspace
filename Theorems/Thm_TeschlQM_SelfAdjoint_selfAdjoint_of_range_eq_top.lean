import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

open ComplexConjugate

/-- Teschl, Lemma 2.3 (p. 63): if `A` is symmetric and `Ran(A + z) = Ran(A + z*) = ℌ` for one
`z ∈ ℂ`, then `A` is self-adjoint. -/
theorem selfAdjoint_of_range_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ)
    (hz : rangeAdd A z = ⊤) (hz' : rangeAdd A (conj z) = ⊤) :
    IsSelfAdjoint A := by sorry

end TeschlQM.SelfAdjoint
