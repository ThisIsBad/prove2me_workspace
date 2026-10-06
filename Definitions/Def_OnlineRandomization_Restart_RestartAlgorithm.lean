import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model

namespace OnlineRandomization.Restart

open Classical in
/-- p. 17: `r ∈ R_H` iff every proper prefix `r'` of `r` (`r' ≠ r`) has `c(r') ≤ H`. -/
def InRH {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ) (r : List R) : Prop :=
  ∀ r' : List R, r' <+: r → r' ≠ r → F.opt r' ≤ H

open Classical in
/-- p. 18: one step of the restart rule on a new request `x`. The state is
`(closed segments, current segment)`. If the current segment is nonempty and appending `x`
leaves `R_H`, the current segment is closed and a new one starts with `x` ("the algorithm
starts over, as if it had not received any previous requests"); otherwise `x` is appended to
the current segment. -/
noncomputable def restartStep {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (s : List (List R) × List R) (x : R) : List (List R) × List R :=
  if s.2 ≠ [] ∧ ¬ InRH F H (s.2 ++ [x]) then (s.1 ++ [s.2], [x]) else (s.1, s.2 ++ [x])

/-- The state of the restart rule after reading the requests `r` in order. -/
noncomputable def restartState {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) : List (List R) × List R :=
  r.foldl (restartStep F H) ([], [])

/-- The current segment after the requests `r`: the requests received since the last restart. -/
noncomputable def currentSegment {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) : List R :=
  (restartState F H r).2

/-- p. 18: the decomposition `r = r(1) r(2) ⋯ r(t)` of a request sequence into segments
(the closed segments followed by the current one; `[]` for `r = []`). -/
noncomputable def segments {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) : List (List R) :=
  if (restartState F H r).2 = [] then (restartState F H r).1
  else (restartState F H r).1 ++ [(restartState F H r).2]

/-- p. 18: the restart algorithm built from `A_H`: on requests `r_1, …, r_i` it answers as
`A_H` answers the current segment, i.e. it simulates `A_H` and starts over whenever the
request sequence leaves `R_H`. -/
noncomputable def restart {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (AH : DetAlg R A) : DetAlg R A :=
  fun r => AH (currentSegment F H r)

end OnlineRandomization.Restart
