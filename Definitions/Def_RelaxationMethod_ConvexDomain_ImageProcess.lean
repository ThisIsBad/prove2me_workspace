import Mathlib

namespace RelaxationMethod.ConvexDomain

/-- `q` is a point of `A` nearest to `p`: `q ∈ A` and `|p - q| ≤ |p - a|` for every `a ∈ A`
(Motzkin–Schoenberg 1954, §9, p. 402). -/
def IsNearestPoint {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p q : EuclideanSpace ℝ (Fin n)) : Prop :=
  q ∈ A ∧ ∀ a ∈ A, dist p q ≤ dist p a

/-- §9, (3.1), p. 402: `p₁` is the image of `p` with respect to `A`, i.e.
`p₁ = p + 2(q - p)` where `q` is the point of `A` nearest to `p` (reflexion of `p` through `q`). -/
def IsImage {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p p₁ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ q, IsNearestPoint A p q ∧ p₁ = p + (2 : ℝ) • (q - p)

/-- §9, (3.2), p. 402: `p₀, p₁, p₂, …` is a run of the reflexion process with respect to `A`:
whenever `p_ν ∉ A`, the next point is the image `p_{ν+1} = F(p_ν)`. Once a point lies in `A`
the process has terminated and later terms are unconstrained. -/
def IsImageRun {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ν : ℕ, p ν ∉ A → IsImage A (p ν) (p (ν + 1))

end RelaxationMethod.ConvexDomain
