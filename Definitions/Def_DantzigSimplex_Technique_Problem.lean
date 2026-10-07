import Mathlib

namespace DantzigSimplex.Technique

/-- Dantzig's equality-form maximization problem (4)--(6). -/
structure Problem (m n : ℕ) where
  col : Fin n → Fin m → ℝ
  rhs : Fin m → ℝ
  cost : Fin n → ℝ

def Problem.combine {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : Fin m → ℝ :=
  fun a => ∑ j, w j * p.col j a

def Problem.objective {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * p.cost j

def Problem.Feasible {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ p.combine w = p.rhs

def Problem.MaximumFeasible {m n : ℕ} (p : Problem m n) (w : Fin n → ℝ) : Prop :=
  p.Feasible w ∧ ∀ v, p.Feasible v → p.objective v ≤ p.objective w

def Problem.Unbounded {m n : ℕ} (p : Problem m n) : Prop :=
  ∀ M : ℝ, ∃ w, p.Feasible w ∧ M < p.objective w

end DantzigSimplex.Technique
