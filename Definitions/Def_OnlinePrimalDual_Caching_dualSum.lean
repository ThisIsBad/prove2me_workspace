import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance

namespace OnlinePrimalDual.Caching

/-- The accumulated dual value `∑_{t | v ∈ S t} y t` charged against primal variable `v`'s dual
constraint, i.e. the left-hand-side sum `∑_{t(p,j)+1 ≤ t ≤ t(p,j+1)-1} y(t)` of inequality (7.1),
p. 152, PDF p. 63, before subtracting `z(p,j)`. Used both to state the dual near-feasibility bound
(Eq. (7.2), p. 155) and, in the algorithm's own update rule, as (part of) the argument driving
`cachingX`'s exponential increase. -/
def dualSum {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (v : V) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => v ∈ inst.S t), y t

end OnlinePrimalDual.Caching
