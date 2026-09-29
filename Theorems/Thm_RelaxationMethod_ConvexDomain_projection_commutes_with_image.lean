import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess

namespace RelaxationMethod.ConvexDomain

/-- §10, p. 404: let `A` lie in the flat `L` and let `π` be the orthogonal projection on `L`.
(i) A point `q ∈ A` is nearest to `p` iff it is nearest to `π p`.
(ii) If `p₁ = F(p)` then `π p₁ = F(π p)` (in the relational sense of `IsImage`, which at a point
of `A` returns the point itself), `p₁` lies on the other side of `L` from `p`
(`p₁ - π p₁ = -(p - π p)`), and `dist (p₁, L) = dist (p, L)`. -/
theorem projection_commutes_with_image {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L] (hAL : A ⊆ L)
    (p p₁ : EuclideanSpace ℝ (Fin n)) :
    (∀ q ∈ A, ((∀ a ∈ A, dist p q ≤ dist p a) ↔
      (∀ a ∈ A, dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) q ≤
        dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) a))) ∧
    (IsImage A p p₁ →
      IsImage A (EuclideanGeometry.orthogonalProjection L p)
          (EuclideanGeometry.orthogonalProjection L p₁) ∧
        p₁ - (EuclideanGeometry.orthogonalProjection L p₁ : EuclideanSpace ℝ (Fin n)) =
          -(p - (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n))) ∧
        Metric.infDist p₁ (L : Set (EuclideanSpace ℝ (Fin n))) =
          Metric.infDist p (L : Set (EuclideanSpace ℝ (Fin n)))) := by sorry

end RelaxationMethod.ConvexDomain

