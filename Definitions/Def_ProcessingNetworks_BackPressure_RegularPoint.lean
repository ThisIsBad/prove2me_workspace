import Mathlib

namespace ProcessingNetworks.BackPressure

/-- Definition 8.7 (regular point), restated from mission V's `RegularPoint` (drafts in this
series do not import one another): a point `t > 0` is regular for a fluid model solution
`(D,F,T,Z)` if all four components are differentiable at `t`. -/
def RegularPoint {I J : ℕ} (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (t : ℝ) : Prop :=
  DifferentiableAt ℝ Dh t ∧ DifferentiableAt ℝ Fh t ∧ DifferentiableAt ℝ Th t ∧
    DifferentiableAt ℝ Zh t

end ProcessingNetworks.BackPressure
