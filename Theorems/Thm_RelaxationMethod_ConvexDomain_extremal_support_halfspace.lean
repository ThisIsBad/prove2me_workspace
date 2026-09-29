import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_ConvexDomain_SupportHalfSpace

namespace RelaxationMethod.ConvexDomain

/-- §9, p. 402: for `p ∉ A` with nearest point `q`, the half-space `H₀` bounded by the hyperplane
through `q` normal to `pq` and not containing `p` belongs to `F`, has distance `|p - q|` from `p`,
maximizes the distance from `p` over `F`, and the reflexion step with respect to any maximizing
`H ∈ F` produces `p + 2(q - p)`. -/
theorem extremal_support_halfspace {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p q : EuclideanSpace ℝ (Fin n)) (hp : p ∉ A) (hq : IsNearestPoint A p q)
    (H₀ : Set (EuclideanSpace ℝ (Fin n)))
    (hH₀ : H₀ = {x | inner ℝ (q - p) q ≤ inner ℝ (q - p) x}) :
    IsSupportHalfSpace A H₀ ∧ p ∉ H₀ ∧ Metric.infDist p H₀ = dist p q ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H ≤ Metric.infDist p H₀) ∧
      (∀ H, IsSupportHalfSpace A H → Metric.infDist p H = Metric.infDist p H₀ →
        ∀ q' ∈ H, dist p q' = Metric.infDist p H →
          p + (2 : ℝ) • (q' - p) = p + (2 : ℝ) • (q - p)) := by sorry

end RelaxationMethod.ConvexDomain

