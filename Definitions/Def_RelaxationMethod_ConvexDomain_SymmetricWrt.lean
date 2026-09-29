import Mathlib

namespace RelaxationMethod.ConvexDomain

/-- Theorem 3, p. 402: the points `u` and `v` are symmetric with respect to the flat `L`:
their midpoint lies in `L` and `u - v` is orthogonal to the direction of `L`
(equivalently, `v` is the point reflection of `u` through its orthogonal projection on `L`). -/
def IsSymmetricWrt {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (u v : EuclideanSpace ℝ (Fin n)) : Prop :=
  midpoint ℝ u v ∈ L ∧ ∀ w ∈ L.direction, inner ℝ (u - v) w = 0

end RelaxationMethod.ConvexDomain
