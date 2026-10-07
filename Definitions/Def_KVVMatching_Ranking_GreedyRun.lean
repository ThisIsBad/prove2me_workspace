import Mathlib

namespace KVVMatching.Ranking

/-- A partial matching is a set of pairs with no repeated vertex on either side. -/
def IsMatching {n : ℕ} (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)

/-- Whether the first vertex of a pair is covered by a matching. -/
def firstMatched {n : ℕ} (M : Finset (Fin n × Fin n)) (i : Fin n) : Prop :=
  ∃ e ∈ M, e.1 = i

/-- Whether the second vertex of a pair is covered by a matching. -/
def secondMatched {n : ℕ} (M : Finset (Fin n × Fin n)) (j : Fin n) : Prop :=
  ∃ e ∈ M, e.2 = j

/-- Greedy online matching. `arrivals t` arrives at time `t`; `rank r` is the
opposite-side vertex of priority `r`, with smaller priorities preferred.
The refusal rule sees the time, this run's current matching, and the arrival. -/
noncomputable def greedyRun {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    Finset (Fin n × Fin n) := by
  classical
  exact (List.range n).foldl (fun M t =>
    if ht : t < n then
      let a : Fin n := ⟨t, ht⟩
      let v := arrivals a
      if refuse t M v then M else
        let eligible : Finset (Fin n) := Finset.univ.filter
          (fun r => adj v (rank r) ∧ ¬ secondMatched M (rank r))
        if he : eligible.Nonempty then
          insert (v, rank (eligible.min' he)) M
        else M
    else M) ∅

end KVVMatching.Ranking
