import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.NoWait

open ProjSchedTW.Complexity (BSym encNats)

/-! # The no-wait flow shop `n|m|F,no wait|k` (Section 3, pp. 6–7; p. 24)

Jobs are `Fin n`, machines are `Fin m` (0-based: the paper's `M_i` is machine `i - 1`). Every
job visits the machines in the order `M_1, …, M_m` (flow shop, `ℓ = F`), and `p ℓ r ∈ ℕ` is the
processing time of job `ℓ` on machine `r`. -/

/-- The partial sum `q_{ℓ i} = Σ_{r=1}^{i} p_{ℓ r}` of (8), p. 24: the total processing time of
job `ℓ` on its first `i` machines (`q_{ℓ 0} = 0`, `q_{ℓ m}` the total processing time). -/
def cum {n m : ℕ} (p : Fin n → Fin m → ℕ) (ℓ : Fin n) (i : ℕ) : ℕ :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin m => r.val < i), p ℓ r

/-- A no-wait schedule is the vector `B` of job starting times `B_ℓ ∈ ℕ`. Under "no wait",
`C_ℓ = B_ℓ + Σ_r p_{ℓ r}` (p. 7), so the operation of job `ℓ` on machine `r` occupies the
half-open interval `[B_ℓ + q_{ℓ r}, B_ℓ + q_{ℓ,r+1})`. The schedule is feasible iff, for every
two distinct jobs and every machine, these two intervals are disjoint (a zero-length operation
occupies the empty interval). Release dates are `0` (times are in `ℕ`).

Formalization Note: start times are natural numbers. Section 3 computes all times from
processing orders on nonnegative integer data, so they are integers; the criteria are regular,
so real start times would give the same yes-instances. -/
def IsNoWaitSchedule {n m : ℕ} (p : Fin n → Fin m → ℕ) (B : Fin n → ℕ) : Prop :=
  ∀ j k : Fin n, j ≠ k → ∀ r : Fin m,
    Disjoint (Set.Ico (B j + cum p j r.val) (B j + cum p j (r.val + 1)))
      (Set.Ico (B k + cum p k r.val) (B k + cum p k (r.val + 1)))

/-- The completion time `C_ℓ = B_ℓ + q_{ℓ m}` of job `ℓ` in the no-wait schedule `B`. -/
def completion {n m : ℕ} (p : Fin n → Fin m → ℕ) (B : Fin n → ℕ) (ℓ : Fin n) : ℕ :=
  B ℓ + cum p ℓ m

/-- The delay `c_{jk}` of formula (9), p. 24: `c_{jk} = max_{1 ≤ i ≤ m} {q_{j i} − q_{k,i−1}}`,
computed in `ℤ`. The maximum is over the machines `r = i − 1 ∈ Fin m`, which form a nonempty
set because `0 < m`. -/
def delay {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (j k : Fin n) : ℤ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))

/-- The length of the travelling-salesman path through the jobs in the order
`π 0, π 1, …, π (n-1)` (p. 24, TRAVELLING SALESMAN on `V = {0, …, n}` with `c_{0ℓ} = 0`,
`c_{ℓ0} = q_{ℓ m}`): `Σ_{i < n-1} c_{π i, π (i+1)} + q_{π (n-1), m}`. For `n = 0` it is `0`. -/
def pathMakespan {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (π : Fin n ≃ Fin n) : ℤ :=
  ∑ i : Fin n, if h : i.val + 1 < n then delay p hm (π i) (π ⟨i.val + 1, h⟩)
    else (cum p (π i) m : ℤ)

/-- The total completion time of the left-justified no-wait schedule that processes the jobs in
the order `π 0, …, π (n-1)` with consecutive start-time gaps `c_{π i, π (i+1)}`: the `k`-th job
`π k` completes at `Σ_{i < k} c_{π i, π (i+1)} + q_{π k, m}`, and this definition sums these
values over `k`. -/
def pathTotalCompletion {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (π : Fin n ≃ Fin n) : ℤ :=
  ∑ k : Fin n,
    ((∑ i : Fin n, if h : i.val < k.val then
        delay p hm (π i) (π ⟨i.val + 1, by have := k.isLt; omega⟩) else 0)
      + (cum p (π k) m : ℤ))

/-- The code of the pair (instance, threshold `y`) of a no-wait flow shop with `n` jobs and `m`
machines: the list `n, m, p_{0,0}, …, p_{0,m-1}, p_{1,0}, …, p_{n-1,m-1}, y` written in binary
with `encNats`. It determines `n`, `m`, `p` and `y`. -/
def nwCode {n m : ℕ} (p : Fin n → Fin m → ℕ) (y : ℕ) : List BSym :=
  encNats ([n, m] ++ (List.ofFn fun ℓ : Fin n => List.ofFn fun r : Fin m => p ℓ r).flatten ++ [y])

/-- The recognition version of `n|m|F,no wait|C_max` (Section 2, p. 4; Theorem 5(a)): the codes
of the pairs (instance, `y`) for which some feasible no-wait schedule has `C_ℓ ≤ y` for every job,
i.e. `C_max ≤ y`. Every flow shop with any `n`, `m`, `p` belongs to the class. -/
def cmaxLang : CookPvsNP.Lang BSym :=
  { w | ∃ (n m : ℕ) (p : Fin n → Fin m → ℕ) (y : ℕ),
      (∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y) ∧ w = nwCode p y }

/-- The recognition version of `n|m|F,no wait,w_j=1|Σw_jC_j` (Theorem 5(b)): the codes of the
pairs (instance, `y`) for which some feasible no-wait schedule has `Σ_ℓ C_ℓ ≤ y`. All weights are
`1` (a class restriction), so no weights are coded. -/
def sumCLang : CookPvsNP.Lang BSym :=
  { w | ∃ (n m : ℕ) (p : Fin n → Fin m → ℕ) (y : ℕ),
      (∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y) ∧ w = nwCode p y }

end SchedComplexity.NoWait
