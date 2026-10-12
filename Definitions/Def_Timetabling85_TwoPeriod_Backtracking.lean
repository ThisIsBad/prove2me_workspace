import Mathlib

namespace Timetabling85.TwoPeriod

/-- Implications of a set `S` of chosen schedules in a conflict graph on `Fin n × Bool`
(node `(j, true)` is x_j, node `(j, false)` is x̄_j): the least set containing `S` and such
that whenever `u` is in it and `u` is linked to a node `w` of another teacher, the other
schedule `(w.1, !w.2)` of that teacher is in it. -/
inductive InClosure {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (S : Set (Fin n × Bool)) :
    Fin n × Bool → Prop
  | base {u : Fin n × Bool} : u ∈ S → InClosure G S u
  | force {u w : Fin n × Bool} : InClosure G S u → G.Adj u w → w.1 ≠ u.1 →
      InClosure G S (w.1, !w.2)

/-- All the implications of the chosen schedules `S`, as a finite set. -/
noncomputable def closure {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (S : Finset (Fin n × Bool)) : Finset (Fin n × Bool) := by
  classical
  exact Finset.univ.filter (InClosure G (S : Set (Fin n × Bool)))

/-- Teacher `j` has a fixed schedule in `A`. -/
def Fixed {n : ℕ} (A : Finset (Fin n × Bool)) (j : Fin n) : Prop :=
  (j, true) ∈ A ∨ (j, false) ∈ A

instance {n : ℕ} (A : Finset (Fin n × Bool)) (j : Fin n) : Decidable (Fixed A j) :=
  inferInstanceAs (Decidable ((j, true) ∈ A ∨ (j, false) ∈ A))

/-- States of the limited backtracking: `run A` with `A` the schedules fixed so far, or `fail`
(no timetable exists). -/
inductive State (n : ℕ) where
  | run (A : Finset (Fin n × Bool))
  | fail

/-- One move of the limited backtracking of the proof of Proposition 2.4 (pp. 154–155).
From `run A`, for any teacher `j` not yet fixed and any first choice `b` (the arbitrary
decision): if the implications of `A ∪ {(j, b)}` are pairwise non-adjacent the decision is kept;
otherwise the decision is reversed if the implications of `A ∪ {(j, !b)}` are pairwise
non-adjacent; otherwise the procedure fails. A `run A` with every teacher fixed and `fail` have
no moves. -/
inductive Step {n : ℕ} (G : SimpleGraph (Fin n × Bool)) : State n → State n → Prop
  | keep {A : Finset (Fin n × Bool)} {j : Fin n} {b : Bool} :
      ¬ Fixed A j →
      G.IsIndepSet (closure G (insert (j, b) A) : Set (Fin n × Bool)) →
      Step G (State.run A) (State.run (closure G (insert (j, b) A)))
  | reverse {A : Finset (Fin n × Bool)} {j : Fin n} {b : Bool} :
      ¬ Fixed A j →
      ¬ G.IsIndepSet (closure G (insert (j, b) A) : Set (Fin n × Bool)) →
      G.IsIndepSet (closure G (insert (j, !b) A) : Set (Fin n × Bool)) →
      Step G (State.run A) (State.run (closure G (insert (j, !b) A)))
  | fail {A : Finset (Fin n × Bool)} {j : Fin n} {b : Bool} :
      ¬ Fixed A j →
      ¬ G.IsIndepSet (closure G (insert (j, b) A) : Set (Fin n × Bool)) →
      ¬ G.IsIndepSet (closure G (insert (j, !b) A) : Set (Fin n × Bool)) →
      Step G (State.run A) State.fail

/-- The states reachable from the initial state `run ∅` (nothing fixed). -/
def Reachable {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (s : State n) : Prop :=
  Relation.ReflTransGen (Step G) (State.run ∅) s

end Timetabling85.TwoPeriod
