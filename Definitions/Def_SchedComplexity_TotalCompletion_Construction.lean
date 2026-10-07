import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.TotalCompletion

/-! # The construction of Theorem 4(a)

Brucker, Lenstra & Rinnooy Kan 1975, proof of Theorem 4(a), p. 22: from a KNAPSACK instance
`a_1, …, a_t, b` (items indexed by `Fin t`, 0-based) build an instance of
`n|1|r_n≥0,w_j=1|Σw_jC_j` and a threshold `y`. Every constant below is the one printed on p. 22,
with `A = Σ_{j∈T} a_j` and `a_* = max_{j∈T} a_j` (p. 16). -/

variable {t : ℕ}

/-- `A = Σ_{j∈T} a_j` (p. 16). -/
def sumA (a : Fin t → ℕ) : ℕ := ∑ i, a i

/-- `t' = t(t + 1)a_*`. -/
def tPrime (a : Fin t → ℕ) : ℕ := t * (t + 1) * SchedComplexity.Tardiness.aStar a

/-- `τ = (t' + 1)(b + 1) + t'`. -/
def tau (a : Fin t → ℕ) (b : ℕ) : ℕ := (tPrime a + 1) * (b + 1) + tPrime a

/-- `u = ½(t + t')(t + t' + 1)τ + (t + 1)τ`. The product `(t + t')(t + t' + 1)` is even, so the
natural-number division by `2` is exact. The paper uses `u` twice: as the number of jobs in the
group `U`, and as the bound `Σ_{j∉U} C_j ≤ u` in the proof (p. 22 shows that the forward
schedule's bound equals this `u`). -/
def uCount (a : Fin t → ℕ) (b : ℕ) : ℕ :=
  (t + tPrime a) * (t + tPrime a + 1) / 2 * tau a b + (t + 1) * tau a b

/-- `σ = Σ_{j∉U} p_j1 = (t + t')τ + A + 1`; the definition is the closed form printed on p. 22. -/
def sigma (a : Fin t → ℕ) (b : ℕ) : ℕ := (t + tPrime a) * tau a b + sumA a + 1

/-- `υ = u(σ + 1)`. -/
def upsilon (a : Fin t → ℕ) (b : ℕ) : ℕ := uCount a b * (sigma a b + 1)

/-- The threshold `y = υ + ½u(u + 1)υ`; `u(u + 1)` is even, so the division by `2` is exact. -/
def yThreshold (a : Fin t → ℕ) (b : ℕ) : ℕ :=
  upsilon a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b

/-- The number of jobs `n = t + t' + u + 1`. -/
def numJobs (a : Fin t → ℕ) (b : ℕ) : ℕ := t + tPrime a + uCount a b + 1

/-- The four groups of jobs, as ranges of the 0-based index `j` (the paper's `J_{j+1}`):
`T = {1, …, t}` is `j < t`; `T' = {t+1, …, t+t'}` is `t ≤ j < t + t'`;
`U = {t+t'+1, …, t+t'+u}` is `t + t' ≤ j < t + t' + u`; and the last job `J_n` is
`j = t + t' + u`. -/
def groupT (a : Fin t → ℕ) (b : ℕ) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => j.val < t

/-- The group `T' = {t+1, …, t+t'}` (0-based indices `t, …, t + t' - 1`). -/
def groupT' (a : Fin t → ℕ) (b : ℕ) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => t ≤ j.val ∧ j.val < t + tPrime a

/-- The group `U = {t+t'+1, …, t+t'+u}` (0-based indices `t + t', …, t + t' + u - 1`). -/
def groupU (a : Fin t → ℕ) (b : ℕ) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => t + tPrime a ≤ j.val ∧ j.val < t + tPrime a + uCount a b

/-- The last job `J_n` (0-based index `n - 1 = t + t' + u`). -/
def lastJob (a : Fin t → ℕ) (b : ℕ) : Fin (numJobs a b) :=
  ⟨t + tPrime a + uCount a b, by unfold numJobs; omega⟩

/-- Processing times: `p_j1 = τ + a_j` (`j ∈ T`), `p_j1 = τ` (`j ∈ T'`), `p_j1 = υ` (`j ∈ U`),
`p_n1 = 1`. -/
def procTime (a : Fin t → ℕ) (b : ℕ) (j : Fin (numJobs a b)) : ℕ :=
  if h : j.val < t then tau a b + a ⟨j.val, h⟩
  else if j.val < t + tPrime a then tau a b
  else if j.val < t + tPrime a + uCount a b then upsilon a b
  else 1

/-- Release dates: `r_j = 0` for every job but the last, `r_n = tτ + b`. -/
def release (a : Fin t → ℕ) (b : ℕ) (j : Fin (numJobs a b)) : ℕ :=
  if j.val = t + tPrime a + uCount a b then t * tau a b + b else 0

/-- Weights: `w_j = 1` for every job. -/
def weight (a : Fin t → ℕ) (b : ℕ) (_j : Fin (numJobs a b)) : ℕ := 1

/-- For a set `S` of items, the jobs `{J_j | j ∈ S} ⊆ T`. -/
def jobsT (a : Fin t → ℕ) (b : ℕ) (S : Finset (Fin t)) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => ∃ i ∈ S, j.val = i.val

/-- For a set `S` of items, the jobs `{J_{t+j} | j ∈ S}`; for `S = T − S₀` this is the set `S'`
of the forward direction on p. 22 (a subset of `T'` when `t ≤ t'`). -/
def jobsShift (a : Fin t → ℕ) (b : ℕ) (S : Finset (Fin t)) : Finset (Fin (numJobs a b)) :=
  Finset.univ.filter fun j => ∃ i ∈ S, j.val = t + i.val

end SchedComplexity.TotalCompletion
