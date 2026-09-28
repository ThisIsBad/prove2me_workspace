import Mathlib

namespace ChanPangGQVI.Shared

/-- Chan and Pang 1982, p. 220, Theorem 5.1: `p` is a nearest point of the set `S` to the point
`z`, i.e. `p ∈ S` and `‖p - z‖ ≤ ‖q - z‖` for every `q ∈ S` ("`p` solves `min_{x ∈ S} ‖x - z‖`").
The norm is the Euclidean norm of `EuclideanSpace ℝ (Fin n)`. -/
def IsProj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (z p : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  p ∈ S ∧ ∀ q ∈ S, ‖p - z‖ ≤ ‖q - z‖

/-- Chan and Pang 1982, p. 220: the projection `P_S(z) = sol min_{x ∈ S} ‖x - z‖` of the point
`z` on the set `S`. When a nearest point exists it is returned (for a nonempty closed convex `S`
it exists and is unique, so this is the paper's `P_S(z)`); otherwise the junk value `z` is
returned. Every statement of this series that uses `proj` assumes `S` nonempty, closed and
convex, so the junk branch is never reached there. -/
noncomputable def proj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  by
    classical
    exact if h : ∃ p, IsProj S z p then h.choose else z

end ChanPangGQVI.Shared
