import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
open Filter Topology

namespace RelaxationMethod.ConvexDomain

/-- §10, p. 403 (by the argument of §5, p. 399): if the reflexion process with respect to a
closed bounded convex set `A` produces an infinite sequence converging to `a`, then `a ∈ A` and
`a` lies on the boundary of `A`. -/
theorem limit_mem_frontier {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) (hinf : ∀ ν : ℕ, p ν ∉ A)
    (a : EuclideanSpace ℝ (Fin n)) (ha : Tendsto p atTop (𝓝 a)) :
    a ∈ A ∧ a ∈ frontier A := by sorry

end RelaxationMethod.ConvexDomain
