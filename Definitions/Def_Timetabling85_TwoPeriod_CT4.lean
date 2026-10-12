import Mathlib

namespace Timetabling85.TwoPeriod

/-- The data of the daily class–teacher problem CT4 with preassignments and unavailabilities
(de Werra 1985, §2.2, p. 154): `m` classes, `n` teachers, `p` periods,
`rbar i j` = r̄_ij (lectures of class `i` with teacher `j` still to schedule),
`bbar i k` = b̄_ik (class `i` available and not preassigned at period `k`),
`cbar j k` = c̄_jk (teacher `j` available and not preassigned at period `k`). -/
structure CT4Data (m n p : ℕ) where
  rbar : Fin m → Fin n → ℕ
  bbar : Fin m → Fin p → Bool
  cbar : Fin n → Fin p → Bool

/-- `x i j k = true` encodes x̄_ijk = 1; the Boolean type encodes constraint (15).
`IsSolution I x` is constraints (12)–(14) of CT4. -/
def IsSolution {m n p : ℕ} (I : CT4Data m n p) (x : Fin m → Fin n → Fin p → Bool) : Prop :=
  (∀ i j, (∑ k, (x i j k).toNat) = I.rbar i j) ∧
  (∀ i k, (∑ j, (x i j k).toNat) ≤ (I.bbar i k).toNat) ∧
  (∀ j k, (∑ i, (x i j k).toNat) ≤ (I.cbar j k).toNat)

/-- A schedule of teacher `t_j`: an assignment `y i k` (class `i` meets `t_j` at period `k`)
satisfying the parts of (12)–(15) that involve `t_j` alone: (12) for `j`, (14) for `j`, and
class availability `y i k → b̄_ik` from (13). -/
def IsTeacherSchedule {m n p : ℕ} (I : CT4Data m n p) (j : Fin n)
    (y : Fin m → Fin p → Bool) : Prop :=
  (∀ i, (∑ k, (y i k).toNat) = I.rbar i j) ∧
  (∀ k, (∑ i, (y i k).toNat) ≤ (I.cbar j k).toNat) ∧
  (∀ i k, y i k = true → I.bbar i k = true)

instance {m n p : ℕ} (I : CT4Data m n p) (j : Fin n) :
    DecidablePred (IsTeacherSchedule I j) := fun y => by
  unfold IsTeacherSchedule; infer_instance

/-- The finite set of possible schedules of teacher `t_j`. -/
def schedules {m n p : ℕ} (I : CT4Data m n p) (j : Fin n) :
    Finset (Fin m → Fin p → Bool) :=
  Finset.univ.filter (IsTeacherSchedule I j)

/-- A node of the conflict graph: a teacher together with one of its possible schedules. -/
abbrev Node {m n p : ℕ} (I : CT4Data m n p) : Type :=
  Σ j : Fin n, {y : Fin m → Fin p → Bool // y ∈ schedules I j}

/-- The conflict graph `G` of the proof of Proposition 2.4 (p. 155): two distinct nodes are
linked iff the corresponding schedules are not compatible, i.e. they are two different schedules
of the same teacher, or they put the same class in the same period. -/
def conflictGraph {m n p : ℕ} (I : CT4Data m n p) : SimpleGraph (Node I) :=
  SimpleGraph.fromRel fun u v =>
    u.1 = v.1 ∨ ∃ i k, u.2.1 i k = true ∧ v.2.1 i k = true

end Timetabling85.TwoPeriod
