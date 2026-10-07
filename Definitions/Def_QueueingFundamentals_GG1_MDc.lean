import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.GG1

/-- The Poisson probability `λ^n e^{−λ}/n!` of `n` arrivals in one unit of time (the constant
service time of the M/D/c queue, §6.3, p.294). The arrival rate is `lam` (`λ` is a Lean keyword). -/
noncomputable def poissonProb (lam : ℝ) (n : ℕ) : ℝ :=
  lam ^ n * Real.exp (-lam) / (Nat.factorial n : ℝ)

/-- `P_c = ∑_{n=0}^{c} p_n`, the probability of `c` or fewer in the system (p.295). -/
def cumProb (p : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), p n

/-- The M/D/c steady-state equations (6.17) (p.295), with the service time as the unit of time:
for every `n ≥ 0`,
`p_n = P_c λ^n e^{−λ}/n! + p_{c+1} λ^{n−1} e^{−λ}/(n−1)! + ⋯ + p_{c+n} e^{−λ}`,
i.e. `p_n = P_c·a_n + ∑_{k=1}^{n} p_{c+k} a_{n−k}` with `a_m = λ^m e^{−λ}/m!`
(`n − k` is never truncated since `k ≤ n`). -/
def MDcBalance (lam : ℝ) (c : ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, p n = cumProb p c * poissonProb lam n +
    ∑ k ∈ Finset.Icc 1 n, p (c + k) * poissonProb lam (n - k)

/-- `p` is a steady-state distribution of the M/D/c queue with arrival rate `lam` (per unit
service time): a probability vector on `{0, 1, 2, …}` solving (6.17). -/
def IsMDcStationary (lam : ℝ) (c : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ HasSum p 1 ∧ MDcBalance lam c p

end QueueingFundamentals.GG1
