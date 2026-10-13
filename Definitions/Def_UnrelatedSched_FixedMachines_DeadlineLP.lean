import Mathlib

namespace UnrelatedSched.FixedMachines

/-- The feasible region of the linear program (LP) of the Rounding Theorem
(Lenstra–Shmoys–Tardos, CWI Report OS-R8714, §2, Theorem 1, p. 3), for the sub-instance consisting
of the jobs in `R`.

Machines are `Fin m`, jobs are `Fin n`, `P i j` is the processing time of job `j` on machine `i`,
`dl i` is the deadline `d_i` of machine `i` and `t` is the threshold. The paper's variables `x_ij`
exist only for `j ∈ J_i(t) = {j : p_ij ≤ t}`; here `x` is a full `m × n` real matrix and the
missing variables are pinned to `0` (`t < P i j → x i j = 0`). Jobs outside `R` are not part of
the sub-instance and their columns are pinned to `0` as well. The constraints are
* `∑_{i ∈ M_j(t)} x_ij = 1` for every job `j ∈ R`,
* `∑_{j ∈ J_i(t)} p_ij x_ij ≤ d_i` for every machine `i`,
* `x_ij ≥ 0`.
With `R = Set.univ` this is exactly (LP) of Theorem 1. -/
def DeadlineLP {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (R : Set (Fin n)) (dl : Fin m → ℝ)
    (t : ℝ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {x | (∀ i j, 0 ≤ x i j) ∧
       (∀ i j, t < (P i j : ℝ) → x i j = 0) ∧
       (∀ i j, j ∉ R → x i j = 0) ∧
       (∀ j, j ∈ R → ∑ i, x i j = 1) ∧
       (∀ i, ∑ j, (P i j : ℝ) * x i j ≤ dl i)}

end UnrelatedSched.FixedMachines
