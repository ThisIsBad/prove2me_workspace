import Mathlib
import Definitions.Def_SennottDP_Discounted_MDC

open scoped ENNReal NNReal

namespace SennottDP.BOR

/-- Sennott (1999), §2.2, p. 20: a (deterministic) stationary policy `f` chooses the action
`f(i) ∈ A_i` whenever the current state is `i`. -/
def StationaryPolicy {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) : Type :=
  {f : S → Act // ∀ i, f i ∈ M.A i}

/-- Sennott (1999), §2.2, p. 21: a randomized stationary policy `d` chooses, whenever the current
state is `i`, the action `a ∈ A_i` with probability `d(a | i)`, independently of the past. -/
structure RandStationaryPolicy {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) where
  /-- `dist i a = d(a | i)` -/
  dist : S → Act → ℝ≥0∞
  /-- no mass outside `A_i` -/
  dist_supp : ∀ i a, a ∉ M.A i → dist i a = 0
  /-- `d(· | i)` is a probability distribution on `A_i` -/
  dist_sum : ∀ i, ∑ a ∈ M.A i, dist i a = 1

/-- A randomized stationary policy viewed as a general policy: after every history `h_n` it uses
the distribution `d(· | i_n)` of the current state. -/
def RandStationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) : SennottDP.Discounted.Policy M where
  dist n s _ a := d.dist (s (Fin.last n)) a
  dist_supp _ _ _ a ha := d.dist_supp _ a ha
  dist_sum _ _ _ := d.dist_sum _

open Classical in
/-- A stationary policy `f` viewed as a randomized stationary policy: `d(a | i) = 1` if
`a = f(i)` and `0` otherwise. -/
noncomputable def StationaryPolicy.toRand {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (f : StationaryPolicy M) : RandStationaryPolicy M where
  dist i a := if a = f.1 i then 1 else 0
  dist_supp i a ha := by
    have hne : a ≠ f.1 i := fun h => ha (h ▸ f.2 i)
    simp [hne]
  dist_sum i := by
    simp [f.2 i]

/-- A stationary policy `f` viewed as a general policy (through its randomized version). -/
noncomputable def StationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type}
    {M : SennottDP.Discounted.MDC S Act} (f : StationaryPolicy M) : SennottDP.Discounted.Policy M :=
  f.toRand.toPolicy

end SennottDP.BOR
