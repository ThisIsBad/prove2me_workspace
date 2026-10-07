import Mathlib

namespace CriticalPath.Events

/-- A project network in the sense of Kelley–Walker (1959), Part I §1, pp. 161–162:
`n + 1` events labelled `0, …, n` (origin `0`, terminus `n`, two distinguished events so `1 ≤ n`),
jobs `(i, j)` given as a finite set `P` of ordered pairs of events, every job's head having a
larger label than its tail, and origin preceding and terminus following every event. -/
structure ProjectNetwork (n : ℕ) where
  /-- The jobs of the project: job `(i, j)` is an arrow from event `i` to event `j`. -/
  P : Finset (Fin (n + 1) × Fin (n + 1))
  /-- There are two distinguished events, origin `0` and terminus `n`. -/
  one_le : 1 ≤ n
  /-- The event at the head of an arrow has a larger label than the event at the tail. -/
  label_lt : ∀ e ∈ P, e.1 < e.2
  /-- Origin precedes every event. -/
  origin_precedes : ∀ k, Relation.ReflTransGen (fun i j => (i, j) ∈ P) 0 k
  /-- Terminus follows every event. -/
  terminus_follows : ∀ k, Relation.ReflTransGen (fun i j => (i, j) ∈ P) k (Fin.last n)

namespace ProjectNetwork

variable {n : ℕ} (N : ProjectNetwork n)

/-- The events `i` with a job `(i, j)` ending at `j`. -/
def pred (j : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => (i, j) ∈ N.P)

/-- The events `j` with a job `(i, j)` starting at `i`. -/
def succ (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j => (i, j) ∈ N.P)

theorem mem_pred {i j : Fin (n + 1)} : i ∈ N.pred j ↔ (i, j) ∈ N.P := by
  simp [pred]

theorem mem_succ {i j : Fin (n + 1)} : j ∈ N.succ i ↔ (i, j) ∈ N.P := by
  simp [succ]

theorem pred_nonempty {j : Fin (n + 1)} (h : j ≠ 0) : (N.pred j).Nonempty := by
  rcases (N.origin_precedes j).cases_tail with h0 | ⟨b, _, hb⟩
  · exact absurd h0 h
  · exact ⟨b, (N.mem_pred).2 hb⟩

theorem succ_nonempty {i : Fin (n + 1)} (h : i ≠ Fin.last n) : (N.succ i).Nonempty := by
  rcases (N.terminus_follows i).cases_head with h0 | ⟨b, hb, _⟩
  · exact absurd h0 h
  · exact ⟨b, (N.mem_succ).2 hb⟩

theorem lt_of_mem_pred {i j : Fin (n + 1)} (h : i ∈ N.pred j) : i < j :=
  N.label_lt (i, j) ((N.mem_pred).1 h)

theorem lt_of_mem_succ {i j : Fin (n + 1)} (h : j ∈ N.succ i) : i < j :=
  N.label_lt (i, j) ((N.mem_succ).1 h)

end ProjectNetwork

end CriticalPath.Events
