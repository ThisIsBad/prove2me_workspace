import Mathlib
import Definitions.Def_AllocationIndices_Achievable

namespace MulticlassQNet.SingleStation

open Finset

/-!
# The multiclass M/M/1 queue: the polyhedra P1 and P2 and the vectors v(π)

Bertsimas, Paschalidis, Tsitsiklis, *Optimization of Multiclass Queueing Networks: Polyhedral and
Nonlinear Characterizations of Achievable Performance*, MIT Sloan WP #3509-92-MSA (Dec. 1992),
§8.1–§8.2, pp. 33–38.

A single server serves `n` customer classes `E = Fin n` (the paper's class `i` is `i.val + 1`).
Class `i` arrives at rate `lam i` (the paper's `λ_i`) and is served at rate `mu i` (`μ_i`); its
traffic intensity is `ρ_i = λ_i / μ_i`. The variable `x i` is the paper's `n_i`, the mean number
of class `i` customers in steady state (renamed because `n` is the number of classes); the
variable `I i j` is the paper's `I_ij`. All objects here are explicit polyhedra and vectors; no
policy or probability appears.
-/

/-- The traffic intensity `ρ_i = λ_i / μ_i` of class `i` (p. 35). -/
noncomputable def rho {n : ℕ} (lam mu : Fin n → ℝ) (i : Fin n) : ℝ := lam i / mu i

/-- The right-hand side of (64)–(65) (p. 35):
`b(S) = (∑_{i∈S} ρ_i/μ_i) / (1 − ∑_{i∈S} ρ_i)`. Under the load condition `∑_i ρ_i < 1` and
`ρ_i > 0` the denominator is positive for every `S`; `b(∅) = 0`. -/
noncomputable def b {n : ℕ} (lam mu : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, rho lam mu i / mu i) / (1 - ∑ i ∈ S, rho lam mu i)

/-- The polyhedron **P1** of Theorem 8.3 (pp. 35–36):
`∑_{i∈S} n_i/μ_i ≥ b(S)` for `S ⊂ E` (64), `∑_{i∈E} n_i/μ_i = b(E)` (65), `n_i ≥ 0`.
It is the base `B(f, b)` of (60) with `f_i^S = 1/μ_i`, i.e. the platform's
`AllocationIndices.achievablePolytope` with the matrix `A S i = 1 / μ_i`. -/
noncomputable def P1 {n : ℕ} (lam mu : Fin n → ℝ) : Set (Fin n → ℝ) :=
  AllocationIndices.achievablePolytope (fun _ i => 1 / mu i) (b lam mu)

/-- The polyhedron **P2** of Theorem 8.4 (p. 38), in the variables `(n_i, I_ij)`:
`μ_i I_ii − λ_i n_i = λ_i` (69); `μ_i I_ij + μ_j I_ji − λ_j n_i − λ_i n_j = 0` for `i ≠ j` (70);
`∑_{i∈E} I_ij = n_j` (71); `n_i, I_ij ≥ 0`. A point is a pair `(x, I)` with `x i = n_i` and
`I i j = I_ij`. -/
def P2 {n : ℕ} (lam mu : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ (∀ i j, 0 ≤ p.2 i j) ∧
    (∀ i, mu i * p.2 i i - lam i * p.1 i = lam i) ∧
    (∀ i j, i ≠ j → mu i * p.2 i j + mu j * p.2 j i - lam j * p.1 i - lam i * p.1 j = 0) ∧
    (∀ j, ∑ i, p.2 i j = p.1 j)}

/-- The vector `v(π)` of (58) (p. 33) for P1, i.e. with `f_i^S = 1/μ_i` and the `b` above.
The permutation `π` lists the classes as `π_k = π ⟨k − 1, _⟩`, and
`AllocationIndices.lowSet π k = {π_1, …, π_k}`. `v(π)` is the unique solution of
`∑_{j=1}^{k} x_{π_j}/μ_{π_j} = b({π_1, …, π_k})` for `k = 1, …, n`; solving the triangular system
gives the closed form used here,
`v(π)_{π_k} = μ_{π_k} · (b({π_1, …, π_k}) − b({π_1, …, π_{k−1}}))`. -/
noncomputable def v {n : ℕ} (lam mu : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  mu i * (b lam mu (AllocationIndices.lowSet π ((π.symm i : ℕ) + 1)) -
    b lam mu (AllocationIndices.lowSet π (π.symm i : ℕ)))

end MulticlassQNet.SingleStation
