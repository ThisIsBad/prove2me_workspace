import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

namespace CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reduced cost `c_p(v, w) = c(v, w) + p(v) - p(w)` for a price function `p : V → ℝ` (p. 877). -/
def reducedCost (N : CircNetwork V) (p : V → ℝ) (v w : V) : ℝ :=
  N.c v w + p v - p w

/-- `f` satisfies the `ε`-optimality constraints (5) with respect to the price function `p`:
`u_f(v, w) > 0 ⇒ c_p(v, w) ≥ -ε` for all `(v, w) ∈ E` (p. 877). -/
def IsEpsOptimalWrt (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) (p : V → ℝ) : Prop :=
  ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → -ε ≤ reducedCost N p v w

/-- For `ε ≥ 0`, a circulation `f` is `ε`-optimal if there is a price function `p` with respect
to which it satisfies the `ε`-optimality constraints (5) (p. 877). -/
def IsEpsOptimal (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) : Prop :=
  IsCirculation N f ∧ 0 ≤ ε ∧ ∃ p : V → ℝ, IsEpsOptimalWrt N f ε p

/-- `ε(f)`, the minimum `ε` such that the circulation `f` is `ε`-optimal (p. 877), as the
infimum of the set of such `ε`. For a circulation this set is nonempty and bounded below by `0`. -/
noncomputable def epsOpt (N : CircNetwork V) (f : V → V → ℝ) : ℝ :=
  sInf {ε : ℝ | IsEpsOptimal N f ε}

/-- An arc `(v, w)` is `ε`-fixed (p. 879) if the flow through it is the same for all
`ε`-optimal circulations. -/
def IsEpsFixed (N : CircNetwork V) (ε : ℝ) (v w : V) : Prop :=
  ∀ g g' : V → V → ℝ, IsEpsOptimal N g ε → IsEpsOptimal N g' ε → g v w = g' v w

end CycleCanceling.MinMean
