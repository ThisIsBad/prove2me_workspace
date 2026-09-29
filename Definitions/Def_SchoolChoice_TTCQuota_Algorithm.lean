import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Model

namespace SchoolChoice.TTCQuota

variable {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype Ty] [DecidableEq Ty]

/-- The best element of a finite set `T` under a ranking `r` (the element of least rank),
or `none` if `T` is empty. -/
def bestIn {α : Type} {n : ℕ} (r : α ≃ Fin n) (T : Finset α) : Option α :=
  if h : T.Nonempty then some (r.symm ((T.image r).min' (h.image r))) else none

/-- The state of the top trading cycles algorithm with type-specific quotas between two
steps: `rem` is the set of remaining students, `cnt s` the (total) counter of school `s`
(seats still available), `tcnt s t` the type-specific counter of school `s` for type `t`,
and `asg i` the school assigned so far to student `i` (`none` while `i` has not been
assigned, and forever if `i` is removed unassigned). -/
structure State (I S Ty : Type) where
  rem : Finset I
  cnt : S → ℕ
  tcnt : S → Ty → ℕ
  asg : I → Option S

/-- The initial state (Step 1, Section III.B, p. 22): every student remains, each school's
counter equals its capacity `q s`, each type-specific counter equals the quota `qt s t` of
the associated type, and nobody is assigned. -/
def init (q : S → ℕ) (qt : S → Ty → ℕ) : State I S Ty :=
  ⟨Finset.univ, q, qt, fun _ => none⟩

/-- The remaining schools: those whose (total) counter is positive. A school is removed
when its total counter reduces to zero, not when a type-specific counter does; a school
of capacity `0` is never remaining. -/
def remSchools (st : State I S Ty) : Finset S :=
  Finset.univ.filter (fun s => 0 < st.cnt s)

/-- The remaining schools which have room for type `t`: positive total counter and
positive type-specific counter for `t`. -/
def roomFor (st : State I S Ty) (t : Ty) : Finset S :=
  Finset.univ.filter (fun s => 0 < st.cnt s ∧ 0 < st.tcnt s t)

/-- **Convention for the gap in the paper.** The paper's step is undefined when a remaining
student has no remaining school with room for her type (she cannot point). At the
beginning of every step, each such *stuck* remaining student is removed unassigned (her
assignment stays `none`). Since counters only decrease, a stuck student stays stuck.
`prune τ st` is the state after this removal. -/
def prune (τ : I → Ty) (st : State I S Ty) : State I S Ty :=
  { st with rem := st.rem.filter (fun i => (roomFor st (τ i)).Nonempty) }

/-- The school a student `i` points to: her favourite school, under her announced
preference `P i`, among the remaining schools which have room for her type `τ i`
(`none` if there is none). -/
def pointS (P : I → Pref S) (τ : I → Ty) (st : State I S Ty) (i : I) : Option S :=
  bestIn (P i) (roomFor st (τ i))

/-- The student a school `s` points to: the remaining student with the highest priority
for `s`, whatever her type (`none` if no student remains). -/
def pointI (pri : S → Priority I) (st : State I S Ty) (s : S) : Option I :=
  bestIn (pri s) st.rem

/-- One round of pointing, from students to students: `i` points to the school
`pointS P τ st i`, which points to the student `pointI pri st (pointS P τ st i)`. -/
def nextO (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty)
    (o : Option I) : Option I :=
  (o.bind (pointS P τ st)).bind (pointI pri st)

/-- A remaining student `i` is in a cycle `(s₁, i₁, s₂, …, s_k, i_k)` of the pointing
graph of state `st` iff following the pointers from `i` (student → school → student)
returns to `i`. Every periodic point of a map on `I` has a period at most `card I`, so it
suffices to look at `n + 1` rounds with `n < card I`. -/
def InCycle (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty)
    (i : I) : Prop :=
  i ∈ st.rem ∧ ∃ n ∈ Finset.range (Fintype.card I),
    (nextO P pri τ st)^[n + 1] (some i) = some i

instance (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty) :
    DecidablePred (InCycle P pri τ st) := fun i => by
  unfold InCycle; infer_instance

/-- The set of students who are in a cycle at state `st`. -/
def cycleStudents (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty)
    (st : State I S Ty) : Finset I :=
  st.rem.filter (InCycle P pri τ st)

/-- One step of the top trading cycles algorithm with type-specific quotas (Section III.B,
p. 22). First the stuck students are removed unassigned (`prune`, the convention above);
then, in the pruned state, every remaining student points to her favourite school with
room for her type and every remaining school points to its highest-priority remaining
student. **All cycles present are executed simultaneously**: every student in a cycle is
assigned a seat at the school she points to and is removed; the counter of each school
is reduced by the number of cycle students pointing to it (one for a school in a cycle,
zero otherwise), and its type-specific counter for type `t` by the number of those
students of type `t`. All other counters stay put. A school whose counter reaches zero
is thereby removed (see `remSchools`). -/
def step (P : I → Pref S) (pri : S → Priority I) (τ : I → Ty) (st : State I S Ty) :
    State I S Ty :=
  let st' := prune τ st
  let C := cycleStudents P pri τ st'
  { rem := st'.rem \ C
    cnt := fun s => st'.cnt s - (C.filter (fun i => pointS P τ st' i = some s)).card
    tcnt := fun s t =>
      st'.tcnt s t - (C.filter (fun i => pointS P τ st' i = some s ∧ τ i = t)).card
    asg := fun i => if i ∈ C then pointS P τ st' i else st'.asg i }

/-- `run q qt τ pri P t` is the state after `t` completed steps of the algorithm, i.e. the
state at the **beginning of Step `t + 1`** in the paper's numbering (`run … 0` is the
beginning of Step 1), before that step's removal of stuck students. -/
def run (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (pri : S → Priority I)
    (P : I → Pref S) (t : ℕ) : State I S Ty :=
  (step P pri τ)^[t] (init q qt)

/-- The top trading cycles mechanism with type-specific quotas (Section III.B, p. 22): the
assignment produced after `card I` steps of the algorithm, run on capacities `q`, type
quotas `qt`, student types `τ`, priorities `pri` and the announced preference profile `P`.
Every step with a remaining student removes at least one student, so `card I` steps
suffice. The value `none` means that the student was removed unassigned under the
stuck-student convention (see `prune`). -/
def ttcq (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (pri : S → Priority I)
    (P : I → Pref S) : I → Option S :=
  (run q qt τ pri P (Fintype.card I)).asg

end SchoolChoice.TTCQuota
