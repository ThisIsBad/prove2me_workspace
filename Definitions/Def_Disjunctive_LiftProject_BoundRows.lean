import Mathlib

namespace Disjunctive.LiftProject

/-- The system `Ãx ≥ b̃` (rows indexed by a finite type `M`) is the LP relaxation of a mixed 0-1
program `min{cx : Ax ≥ b, x ≥ 0, x_j ∈ {0,1}, j ∈ N'}` with the bound constraints folded in, as
in Balas §6 (p. 79): "`P := {x : Ãx ≥ b̃}`, with the inequalities `x ≥ 0` and `x_j ≤ 1`,
`j ∈ N'`, included in `Ãx ≥ b̃`". Concretely, the system contains, for every coordinate `k`, a
row `x_k ≥ 0` (row vector `e_k`, right-hand side `0`), and for every `j ∈ N'` a row `-x_j ≥ -1`
(row vector `-e_j`, right-hand side `-1`). -/
def HasBoundRows {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (Nprime : Finset (Fin n)) : Prop :=
  (∀ k : Fin n, ∃ ρ : M, Atil ρ = Pi.single k 1 ∧ btil ρ = 0) ∧
    ∀ j ∈ Nprime, ∃ ρ : M, Atil ρ = -Pi.single j 1 ∧ btil ρ = -1

end Disjunctive.LiftProject
