import Mathlib

namespace FloydAlgorithms.ShortestPath

/-- The directed link lengths in Algorithm 97. `⊤` denotes an absent link. -/
abbrev LengthMatrix (n : ℕ) := Fin n → Fin n → WithTop ℝ

/-- A path with at least one link and no repeated vertices except that its endpoints
may coincide. In the latter case this is a simple closed path. -/
def IsPath {n : ℕ} (i j : Fin n) (L : ℕ) (p : Fin (L + 1) → Fin n) : Prop :=
  1 ≤ L ∧ p 0 = i ∧ p (Fin.last L) = j ∧
    (∀ a b : Fin L, a ≠ b → p a.castSucc ≠ p b.castSucc) ∧
    (∀ a b : Fin L, a ≠ b → p a.succ ≠ p b.succ)

/-- The sum of the direct-link lengths along a path. Any missing link makes
the length `⊤`. -/
def pathLength {n L : ℕ} (w : LengthMatrix n)
    (p : Fin (L + 1) → Fin n) : WithTop ℝ :=
  ∑ t : Fin L, w (p t.castSucc) (p t.succ)

/-- The minimum length of a simple path from `i` to `j`. The infimum is over
a finite set, and an empty set has value `⊤`. -/
noncomputable def shortestLength {n : ℕ} (w : LengthMatrix n)
    (i j : Fin n) : WithTop ℝ := by
  classical
  exact (Finset.range (n + 1)).inf (fun L =>
    (Finset.univ.filter (fun p : Fin (L + 1) → Fin n => IsPath i j L p)).inf
      (fun p => pathLength w p))

/-- No simple closed path has negative length. A missing-link path has
length `⊤` and automatically satisfies the inequality. -/
def NoNegativeCycle {n : ℕ} (w : LengthMatrix n) : Prop :=
  ∀ (i : Fin n) (L : ℕ) (p : Fin (L + 1) → Fin n),
    IsPath i i L p → 0 ≤ pathLength w p

end FloydAlgorithms.ShortestPath
