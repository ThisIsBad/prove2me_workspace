import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The linear-cost arc function of Eq. (9.11): `fa(t) = γ(a)t` on `[c(a),c̄(a)]`, `+∞`
elsewhere. -/
noncomputable def ArcCostMCFP0 (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (gamma : A → ℝ) (a : A)
    (t : ℝ) : WithTop ℝ :=
  if cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a then ((gamma a * t : ℝ) : WithTop ℝ)
  else ⊤

end DiscreteConvex.NetworkFlowsB
