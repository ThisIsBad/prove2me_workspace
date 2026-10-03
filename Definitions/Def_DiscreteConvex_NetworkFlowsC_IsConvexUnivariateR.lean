import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate real function is convex (a proxy for membership in `C[R→R]`). -/
def IsConvexUnivariateR (g : ℝ → WithTop ℝ) : Prop :=
  (∃ x, g x ≠ ⊤) ∧ ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    g (t * x + (1 - t) * y) ≤ (t : WithTop ℝ) * g x + ((1 - t : ℝ) : WithTop ℝ) * g y

-- ===== Network transformation apparatus (§9.6), integer domain =====

end DiscreteConvex.NetworkFlowsC
