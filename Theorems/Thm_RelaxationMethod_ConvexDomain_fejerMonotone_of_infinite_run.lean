import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone

namespace RelaxationMethod.ConvexDomain

/-- §10, p. 403: an infinite sequence produced by the reflexion process (3.1), (3.2) with respect
to a closed bounded convex set `A` is Fejér-monotone with respect to `A`. -/
theorem fejerMonotone_of_infinite_run {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) (hinf : ∀ ν : ℕ, p ν ∉ A) :
    RelaxationMethod.Shared.IsFejerMonotone A p := by sorry

end RelaxationMethod.ConvexDomain
