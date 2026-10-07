import Mathlib

namespace Gomory58.FractionalCut

def IsInt (r : ℝ) : Prop := ∃ z : ℤ, (z : ℝ) = r

def TableauSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) : Prop :=
  ∀ i, x i = a i 0 + ∑ j : Fin n, a i j.succ * (-t j)

def FeasibleSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) : Prop :=
  TableauSol a x t ∧ (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ t j)

def NonnegIntSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) : Prop :=
  FeasibleSol a x t ∧ (∀ i, IsInt (x i)) ∧ (∀ j, IsInt (t j))

noncomputable def cutValue {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (t : Fin n → ℝ) : ℝ :=
  -Int.fract (a i₀ 0) - ∑ j : Fin n, Int.fract (a i₀ j.succ) * (-t j)

def StarSol {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) : Prop :=
  TableauSol a x t ∧ s = cutValue a i₀ t

def FeasibleStar {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) : Prop :=
  StarSol a i₀ x t s ∧ (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ t j) ∧ 0 ≤ s

def NonnegIntSolStar {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) : Prop :=
  FeasibleStar a i₀ x t s ∧ (∀ i, IsInt (x i)) ∧ (∀ j, IsInt (t j)) ∧ IsInt s

end Gomory58.FractionalCut
