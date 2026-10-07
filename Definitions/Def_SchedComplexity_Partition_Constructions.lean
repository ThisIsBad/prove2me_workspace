import Mathlib

namespace SchedComplexity.Partition

/-- `A = Σ_{j ∈ T} a_j` (proof of Theorem 3, p. 15), for the PARTITION data `a_1, …, a_t`
(the list `a`, indices `j < t`). -/
def totalA (a : List ℕ) : ℕ :=
  ∑ j : Fin a.length, a.get j

/-- Construction (a) of Theorem 3 (p. 15): `n = t` jobs with `p_{j1} = a_j`. -/
def procA (a : List ℕ) : Fin a.length → ℕ :=
  fun j => a.get j

/-- The threshold of construction (a): `y = ½A`, a rational number (a real here). -/
noncomputable def yA (a : List ℕ) : ℝ :=
  (totalA a : ℝ) / 2

/-- Construction (b) of Theorem 3 (p. 15): `n = t` jobs with `p_{j1} = w_j = a_j`; this is the
common vector of processing times and weights. -/
def procB (a : List ℕ) : Fin a.length → ℕ :=
  fun j => a.get j

/-- `Σ_{j,k ∈ T, j ≤ k} a_j a_k`: the sum over index pairs `j ≤ k`, the diagonal `j = k`
included. -/
def pairSum (a : List ℕ) : ℕ :=
  ∑ j : Fin a.length, ∑ k : Fin a.length, if j ≤ k then a.get j * a.get k else 0

/-- The threshold of construction (b): `y = Σ_{j,k ∈ T, j ≤ k} a_j a_k − ¼A²`, a rational number
(a real here). -/
noncomputable def yB (a : List ℕ) : ℝ :=
  (pairSum a : ℝ) - (totalA a : ℝ) ^ 2 / 4

/-- `k(S)` (proof of Theorem 3(b), p. 15): the value of `Σ w_j C_j` in construction (b) when the
jobs of `S` are on `M_1` and those of `T − S` on `M_2`, each machine working without idle time
from `0`, in closed form: `Σ_{j,k ∈ S, j ≤ k} a_j a_k + Σ_{j,k ∈ T−S, j ≤ k} a_j a_k`. That this
closed form is the schedule value is the content of the milestone `theorem_3b_value_eq_k`. -/
def kVal (a : List ℕ) (S : Finset (Fin a.length)) : ℕ :=
  (∑ j ∈ S, ∑ k ∈ S, if j ≤ k then a.get j * a.get k else 0) +
    ∑ j ∈ Sᶜ, ∑ k ∈ Sᶜ, if j ≤ k then a.get j * a.get k else 0

end SchedComplexity.Partition
