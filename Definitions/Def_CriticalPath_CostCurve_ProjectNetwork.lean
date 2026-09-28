import Mathlib

namespace CriticalPath.CostCurve

/-- A project network in the sense of Kelley–Walker (1959), Part I §1, pp. 161–162.
Events are labelled `0, 1, …, n` (`Fin (n + 1)`); origin is `0` and terminus is `Fin.last n`.
Jobs are arrows `(i, j) ∈ P`, at most one per ordered pair. -/
structure ProjectNetwork (n : ℕ) where
  /-- The set of jobs `(i, j)`: an arrow from event `i` to event `j`. -/
  P : Finset (Fin (n + 1) × Fin (n + 1))
  /-- Origin and terminus are two distinct events. -/
  one_le : 1 ≤ n
  /-- The head of an arrow always has a larger label than its tail. -/
  label_lt : ∀ e ∈ P, e.1 < e.2
  /-- Origin precedes every event. -/
  origin_precedes : ∀ k : Fin (n + 1), Relation.ReflTransGen (fun i j => (i, j) ∈ P) 0 k
  /-- Terminus follows every event. -/
  terminus_follows : ∀ k : Fin (n + 1),
    Relation.ReflTransGen (fun i j => (i, j) ∈ P) k (Fin.last n)

end CriticalPath.CostCurve
