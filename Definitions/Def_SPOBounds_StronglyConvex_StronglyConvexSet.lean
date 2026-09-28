import Mathlib

namespace SPOBounds.StronglyConvex

/-- The normal cone of `S` at `w̄` (arXiv:1905.11488v3, §5.1, p. 23):
`N_S(w̄) = {c : cᵀ(w − w̄) ≤ 0 for all w ∈ S}`, with cost vectors as continuous linear
functionals (so `cᵀx` is `c x`). -/
def normalCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (wbar : E) : Set (StrongDual ℝ E) :=
  {c | ∀ v ∈ S, c (v - wbar) ≤ 0}

/-- `μ̄`-strongly convex set (Definition 5, p. 23): `S` is convex and, for all `w₁, w₂ ∈ S` and
`λ ∈ [0, 1]`, the closed ball `B(λ w₁ + (1 − λ) w₂, (μ̄/2) λ (1 − λ) ‖w₁ − w₂‖²)` is contained
in `S`. The definition requires `μ̄ ≥ 0`; that is carried by the theorems. -/
def StronglyConvexSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μbar : ℝ) (S : Set E) : Prop :=
  Convex ℝ S ∧ ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Metric.closedBall (t • w₁ + (1 - t) • w₂) ((μbar / 2) * t * (1 - t) * ‖w₁ - w₂‖ ^ 2) ⊆ S

end SPOBounds.StronglyConvex
