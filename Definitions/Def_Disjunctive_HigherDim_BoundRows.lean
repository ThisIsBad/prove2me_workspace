import Mathlib

namespace Disjunctive.HigherDim

/-- The system `A x ≥ b` is the LP relaxation `Ãx ≥ b̃` of a mixed 0-1 program with 0-1 index
set `N'`, written as in Balas §7 (p. 91): `K := {x ∈ ℝⁿ : Ax ≥ b, x ≥ 0, x_j ≤ 1, j ∈ N'}
= {x : Ãx ≥ b̃}`, i.e. the bound constraints are folded into the system as rows. Concretely, the
system contains, for every coordinate `k`, a row `x_k ≥ 0` (row vector `e_k`, right-hand side
`0`), and for every `j ∈ N'` a row `-x_j ≥ -1` (row vector `-e_j`, right-hand side `-1`).

Every construction of Chapter 7 (`Mj`/`Pj`, the Lovász-Schrijver `MK`/`NOp`, the Sherali-Adams
`IsXt`/`KtSet`) multiplies *all* rows of the system it is given; under this predicate those rows
include the bound rows, exactly as the book multiplies `Ãx ≥ b̃` (not only `Ax ≥ b`). -/
def HasBoundRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) : Prop :=
  (∀ k : Fin n, ∃ i : Fin m, A i = Pi.single k 1 ∧ b i = 0) ∧
    ∀ j ∈ Nprime, ∃ i : Fin m, A i = -Pi.single j 1 ∧ b i = -1

end Disjunctive.HigherDim
