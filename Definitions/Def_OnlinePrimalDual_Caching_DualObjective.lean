import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance

namespace OnlinePrimalDual.Caching

/-- The dual objective of this chapter's LP (p. 152, PDF p. 63): the caching LP's dual program
maximizes `∑ₜ rhs(t)·y(t) − ∑ᵥ z(v)` subject to `∀v, dualSum y v − z v ≤ c v`, `y,z ≥ 0` — the `z`
term is the dual variable of the primal's own `x(p,j) ≤ 1` box constraint. Named as its own
quantity (new item, added per `CHANGES_REQUESTED.md`'s required fix to `algorithm_competitive_ratio`)
because, unlike `04-framework`'s `CoveringInstance` (whose right-hand side is fixed at `b(j)=1`),
this chapter's `rhs` can be non-positive, so the direct "weak duality against an arbitrary feasible
offline comparison solution" shortcut used there is unsound here without routing explicitly through
this objective (see `Thm_OnlinePrimalDual_Caching_weak_duality`). -/
def DualObjective {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ) : ℝ :=
  ∑ t, inst.rhs t * y t - ∑ v, z v

end OnlinePrimalDual.Caching
