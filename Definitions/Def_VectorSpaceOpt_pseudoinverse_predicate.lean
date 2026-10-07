import Mathlib

namespace VectorSpaceOpt

/-- `B` is the minimum-norm least-squares pseudoinverse of `A` when, for each target `y`,
`B y` minimizes the residual norm and has minimum norm among all residual minimizers. -/
def IsPseudoinverse
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : G →L[ℝ] H) (B : H →L[ℝ] G) : Prop :=
  ∀ y : H,
    (∀ x : G, ‖A (B y) - y‖ ≤ ‖A x - y‖) ∧
    (∀ x : G, (∀ z : G, ‖A x - y‖ ≤ ‖A z - y‖) → ‖B y‖ ≤ ‖x‖)

end VectorSpaceOpt