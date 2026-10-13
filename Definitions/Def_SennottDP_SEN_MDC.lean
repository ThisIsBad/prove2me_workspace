import Mathlib
import Definitions.Def_SennottDP_Discounted_MDC

open scoped ENNReal NNReal

namespace SennottDP.SEN

/-- Sennott (1999), §2.2, p. 20: a stationary policy `f` chooses the action `f(i) ∈ A_i` whenever
the current state is `i`. -/
def StationaryPolicy {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) : Type :=
  {f : S → Act // ∀ i, f i ∈ M.A i}

open Classical in
/-- A stationary policy `f` viewed as a general policy: at every time `n` and after every history
`h_n`, it chooses the action `f(i_n)` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (f : StationaryPolicy M) : SennottDP.Discounted.Policy M where
  dist n s _ a := if a = f.1 (s (Fin.last n)) then 1 else 0
  dist_supp n s _ a ha := by
    have hne : a ≠ f.1 (s (Fin.last n)) := fun h => ha (h ▸ f.2 _)
    simp [hne]
  dist_sum n s _ := by
    simp [f.2 (s (Fin.last n))]

end SennottDP.SEN
