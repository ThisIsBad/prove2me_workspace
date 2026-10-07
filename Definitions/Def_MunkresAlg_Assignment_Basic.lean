import Mathlib

namespace MunkresAlg.Assignment

open Classical

/-- Munkres (1957), §1, p. 32: a set of positions of an `n × n` matrix is *independent* if no two
of them lie in the same line (row or column). Positions are pairs `(row, column)`. -/
def Independent {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2

/-- `S` is a set of independent zeros of the matrix `B`. -/
def IsIndepZeros {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n × Fin n)) : Prop :=
  Independent S ∧ ∀ p ∈ S, B p.1 p.2 = 0

/-- The rows `R` and columns `C` form a set of lines containing all the zeros of `B`
(p. 34, Step 3). The number of lines is `R.card + C.card`. -/
def CoversZeros {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n)) : Prop :=
  ∀ i j, B i j = 0 → i ∈ R ∨ j ∈ C

/-- The maximal number of independent zeros of `B` (the paper's `n_k`, p. 35): the largest
cardinality of a set of independent zeros. The family contains `∅`, so the supremum is over a
finite nonempty family of natural numbers. -/
noncomputable def maxIndepZeros {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).powerset.filter (IsIndepZeros B)).sup Finset.card

end MunkresAlg.Assignment
