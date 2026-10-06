import Mathlib

namespace SecretaryWD.Weighted

/-- A weighted one-to-one assignment has at most one good per agent. -/
def ValidAssignment {n K : ℕ} (s : Fin K → Option (Fin n)) : Prop :=
  ∀ k l e, s k = some e → s l = some e → k = l

/-- The value of an assignment, with unassigned goods contributing zero. -/
def assignmentValue {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (s : Fin K → Option (Fin n)) : ℝ :=
  ∑ k : Fin K, (s k).elim 0 v * w k

/-- Larger value wins; an equal value is resolved in favor of the smaller agent index. -/
def better {n : ℕ} (v : Fin n → ℝ) (e f : Fin n) : Prop :=
  v f < v e ∨ (v e = v f ∧ e.val < f.val)

/-- The zero-based position of an agent in decreasing value order. -/
noncomputable def valueRank {n : ℕ} (v : Fin n → ℝ) (e : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f => better v f e)).card

/-- Give good `k` to the agent of rank `k`, if one exists. -/
noncomputable def optimalAssignment {n K : ℕ} (v : Fin n → ℝ) :
    Fin K → Option (Fin n) := by
  classical
  intro k
  exact if h : ∃ e : Fin n, valueRank v e = k.val then some (Classical.choose h) else none

/-- Offline benchmark: the heaviest good goes to the highest-value agent. -/
noncomputable def OPT {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ) : ℝ :=
  assignmentValue v w (optimalAssignment v)

end SecretaryWD.Weighted
