import Mathlib

namespace RelaxationMethod.Shared

/-- A sequence `q_0, q_1, …` is **Fejér-monotone** with respect to a set `A` (§4, p. 397):
every `q_ν` lies outside `A`, consecutive points are distinct (2.1), and the distance to every
point of `A` is non-increasing, `|q_ν - a| ⩾ |q_{ν+1} - a|` for all `a ∈ A` (2.2). -/
def IsFejerMonotone {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ ν, q ν ∉ A) ∧ (∀ ν, q ν ≠ q (ν + 1)) ∧
    ∀ a ∈ A, ∀ ν, dist (q (ν + 1)) a ≤ dist (q ν) a

end RelaxationMethod.Shared
