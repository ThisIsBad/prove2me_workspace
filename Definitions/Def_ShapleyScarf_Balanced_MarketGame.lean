import Mathlib
noncomputable section

namespace ShapleyScarf.Balanced

def IsSAllocation {N : Type*} [Fintype N] [DecidableEq N]
    (S : Finset N) (P : Matrix N N ℝ) : Prop :=
  (∀ i j, P i j = 0 ∨ P i j = 1) ∧
  (∀ j ∈ S, ∑ i, P i j = 1) ∧
  (∀ i, i ∉ S → ∀ j, P i j = 0) ∧
  (∀ j, j ∉ S → ∀ i, P i j = 0)

def IsSPermutation {N : Type*} [Fintype N] [DecidableEq N]
    (S : Finset N) (P : Matrix N N ℝ) : Prop :=
  IsSAllocation S P ∧ ∀ i, ∑ j, P i j ≤ 1

def acceptableMatrix {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (S : Finset N) (x : N → ℝ) : Matrix N N ℝ :=
  fun i j => if i ∈ S ∧ x i ≤ A i j then 1 else 0

def marketGame {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (S : Finset N) : Set (N → ℝ) :=
  {x | ∃ P : Matrix N N ℝ, IsSPermutation S P ∧
    ∀ i j, P i j ≤ acceptableMatrix A S x i j}

end ShapleyScarf.Balanced
