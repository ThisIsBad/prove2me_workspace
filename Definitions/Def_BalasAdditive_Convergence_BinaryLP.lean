import Mathlib

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- A finite real zero-one minimization problem in inequality form. -/
structure BinaryLP (n m : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

/-- The slack determined by the binary assignment represented by `J`. -/
def BinaryLP.slack {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) (i : Fin m) : ℝ :=
  P.b i - ∑ j ∈ J, P.A i j

/-- The objective value of a binary assignment. -/
def BinaryLP.cost {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) : ℝ :=
  ∑ j ∈ J, P.c j

/-- Binary assignments are feasible exactly when all slacks are nonnegative. -/
def BinaryLP.Feasible {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) : Prop :=
  ∀ i, 0 ≤ P.slack J i

/-- An optimal binary assignment has no more costly feasible competitor. -/
def BinaryLP.Optimal {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) : Prop :=
  P.Feasible J ∧ ∀ K, P.Feasible K → P.cost J ≤ P.cost K

end BalasAdditive.Convergence
