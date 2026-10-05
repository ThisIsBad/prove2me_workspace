import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

namespace OnlineSetCover.Weighted

open OnlinePrimalDual.OnlineSetCover

/-- A state of the weighted online set-cover algorithm of Alon, Awerbuch, Azar, Buchbinder and
Naor (SIAM J. Comput. 39(2), 2009, Section 3, p. 365), for a fixed guess `α`.
* `w` — the current set weights `w_S`;
* `C` — the current cover `𝒞` (only grows);
* `steps` — the number of weight augmentation steps begun so far (Lemmas 3.1, 3.2);
* `pending` — the elements the adversary has not yet given, in arrival order;
* `cur` — `none` between iterations; `some (j, l)` inside the iteration for element `j`, where
  `l` lists the sets of `𝒮_j` still to be visited in the current augmentation step (when `l = []`
  the algorithm is about to test `w_j < 1` again). -/
structure AlgState (X T : Type*) where
  w : T → ℝ
  C : Finset T
  steps : ℕ
  pending : List X
  cur : Option (X × List T)

/-- A configuration of the algorithm: a running state, or the terminal outcome `FAIL`
(step (c), p. 365). -/
inductive Config (X T : Type*) where
  | ok (s : AlgState X T)
  | fail

variable {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]

/-- Step (a) of a weight augmentation for the set `S` (p. 365):
`w_S ← w_S · (1 + 1/(n · c_S))`, with `n = |X|`; all other weights are unchanged. -/
noncomputable def augmentWeight (inst : SetCoverInstance X T) (w : T → ℝ) (S : T) : T → ℝ :=
  Function.update w S (w S * (1 + 1 / ((Fintype.card X : ℝ) * inst.c S)))

/-- The per-set substep (a)–(c) of a weight augmentation step (p. 365) for the set `S`, from
weights `w` and cover `C`, with `Φ = potential inst · · α`. Writing `w'` for the weights after
(a) and `Φ_s = Φ(w, C)` for the potential before (a):
* if `S ∈ C`, the cover is unchanged and the result is `(w', C)` when `Φ(w', C) ≤ Φ_s`;
* if `S ∉ C`, `S` is added when `Φ(w', C ∪ {S}) ≤ Φ_s`; otherwise the cover is unchanged and
  the result is `(w', C)` when `Φ(w', C) ≤ Φ_s`;
* in every other case the potential has increased and the result is `none`, i.e. "FAIL". -/
noncomputable def processSet (inst : SetCoverInstance X T) (α : ℝ) (w : T → ℝ) (C : Finset T)
    (S : T) : Option ((T → ℝ) × Finset T) :=
  let w' := augmentWeight inst w S
  let Φs := potential inst w C α
  if S ∈ C then
    (if potential inst w' C α ≤ Φs then some (w', C) else none)
  else if potential inst w' (insert S C) α ≤ Φs then some (w', insert S C)
  else if potential inst w' C α ≤ Φs then some (w', C)
  else none

/-- The initial state on the arrival sequence `σ` (p. 365): every weight is `1/m²` with
`m = |𝒮|`, the cover is empty, no augmentation step has been performed, nothing has arrived. -/
noncomputable def initState (σ : List X) : AlgState X T where
  w := fun _ => 1 / (Fintype.card T : ℝ) ^ 2
  C := ∅
  steps := 0
  pending := σ
  cur := none

/-- `l` enumerates `𝒮_j` (the sets containing `j`) without repetition, in some order. The paper
does not fix the order in which a step visits `𝒮_j`; the run allows any. -/
def IsEnumeration (inst : SetCoverInstance X T) (j : X) (l : List T) : Prop :=
  l.Nodup ∧ ∀ S, S ∈ l ↔ S ∈ inst.elemSets j

/-- One transition of the algorithm (p. 365).
* `arrive` — between iterations, the adversary gives the next element `j`.
* `finish` — no augmentation step is in progress and `w_j ≥ 1`: the iteration for `j` ends
  (rule 1 if this happens at arrival; the end of rule 2's loop otherwise).
* `startStep` — no augmentation step is in progress and `w_j < 1`: a new weight augmentation
  step begins, visiting `𝒮_j` in an arbitrary order; the step counter increases by one.
* `process` / `processFail` — the next set `S` of the current step undergoes (a)–(c)
  (`processSet`), ending in a new state or in `FAIL`. -/
inductive Step (inst : SetCoverInstance X T) (α : ℝ) : AlgState X T → Config X T → Prop where
  | arrive (s : AlgState X T) (j : X) (rest : List X) :
      s.cur = none → s.pending = j :: rest →
      Step inst α s (.ok { s with pending := rest, cur := some (j, []) })
  | finish (s : AlgState X T) (j : X) :
      s.cur = some (j, []) → 1 ≤ elementWeight inst s.w j →
      Step inst α s (.ok { s with cur := none })
  | startStep (s : AlgState X T) (j : X) (l : List T) :
      s.cur = some (j, []) → elementWeight inst s.w j < 1 → IsEnumeration inst j l →
      Step inst α s (.ok { s with cur := some (j, l), steps := s.steps + 1 })
  | process (s : AlgState X T) (j : X) (S : T) (l : List T) (w' : T → ℝ) (C' : Finset T) :
      s.cur = some (j, S :: l) → processSet inst α s.w s.C S = some (w', C') →
      Step inst α s (.ok { s with w := w', C := C', cur := some (j, l) })
  | processFail (s : AlgState X T) (j : X) (S : T) (l : List T) :
      s.cur = some (j, S :: l) → processSet inst α s.w s.C S = none →
      Step inst α s .fail

/-- The configurations reachable by the algorithm with guess `α` on the arrival sequence `σ`,
from `initState σ`: every intermediate configuration of the run counts ("throughout the
algorithm"), including those between the per-set substeps of an augmentation step. `FAIL` is
terminal. -/
inductive Reachable (inst : SetCoverInstance X T) (α : ℝ) (σ : List X) : Config X T → Prop where
  | init : Reachable inst α σ (.ok (initState σ))
  | step {s : AlgState X T} {c : Config X T} :
      Reachable inst α σ (.ok s) → Step inst α s c → Reachable inst α σ c

end OnlineSetCover.Weighted
