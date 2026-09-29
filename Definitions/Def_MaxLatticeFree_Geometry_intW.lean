import Mathlib

namespace MaxLatticeFree.Geometry

/-- Interior relative to `W` (arXiv:1701.06543v1, p. 8): `int_W(S)` is the set of points `x ∈ S`
such that `B_ε(x) ∩ W ⊆ S` for some `ε > 0`, where `B_ε(x)` is the open Euclidean ball.
This is the interior of `S` in the topology induced on `W` by `ℝⁿ` (for `S ⊆ W`). -/
def intW {n : ℕ} (W S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ∩ W ⊆ S}

/-- Relative interior (arXiv:1701.06543v1, p. 8): `relint(S) = int_{aff(S)}(S)`, the interior of
`S` relative to its affine hull. -/
def relint {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  intW (affineSpan ℝ S : Set (EuclideanSpace ℝ (Fin n))) S

end MaxLatticeFree.Geometry
