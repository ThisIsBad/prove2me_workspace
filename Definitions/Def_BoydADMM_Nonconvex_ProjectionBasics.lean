import Mathlib

namespace BoydADMM.Nonconvex

/-- Number of nonzero entries in a finite real vector (§9.1, p. 74). -/
noncomputable def cardinality {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The cardinality-constrained set `{x | card(x) ≤ c}`. -/
noncomputable def sparseSet {n : ℕ} (c : ℕ) : Set (Fin n → ℝ) :=
  {x | cardinality x ≤ c}

/-- The vector obtained by retaining entries in `I` and zeroing the rest. -/
def restrictTo {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then v i else 0

/-- Squared Euclidean distance for finite real vectors. -/
def sqDist {n : ℕ} (x v : Fin n → ℝ) : ℝ :=
  ∑ i, (x i - v i) ^ 2

/-- The coordinatewise Boolean constraint set. -/
def booleanSet {n : ℕ} : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- Rounding to a nearest Boolean value, choosing zero at a tie. -/
noncomputable def roundBoolean {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if v i ≤ 1 / 2 then 0 else 1

end BoydADMM.Nonconvex
