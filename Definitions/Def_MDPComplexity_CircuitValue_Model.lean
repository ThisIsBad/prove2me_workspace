import Mathlib

namespace MDPComplexity.CircuitValue

open Finset BigOperators

/-- §2 (p. 444): a finite Markov decision process. `S` is the finite state set; at state `s` the
decisions form a nonempty finite type `D s`; making decision `i` at state `s` at time `t` costs
`c s i t` and moves to state `s'` with probability `p s i t s'` (the paper's `p(s, s', i, t)`).
Each row `p s i t ·` is a probability vector. -/
structure MDP (S : Type) [Fintype S] where
  D : S → Type
  [instFintype : ∀ s, Fintype (D s)]
  [instNonempty : ∀ s, Nonempty (D s)]
  c : (s : S) → D s → ℕ → ℝ
  p : (s : S) → D s → ℕ → S → ℝ
  p_nonneg : ∀ s i t s', 0 ≤ p s i t s'
  p_sum_one : ∀ s i t, ∑ s', p s i t s' = 1

attribute [instance] MDP.instFintype MDP.instNonempty

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A policy `δ(s, t)` (p. 444): a decision for every state and every time `t ∈ ℕ`.
Policies are Markov and may depend on time. -/
def MDP.Policy (M : MDP S) : Type := (s : S) → ℕ → M.D s

/-- Probability, under policy `δ` from the initial state `s₀`, of the trajectory
`x 0, x 1, …, x T` (states at times `0, …, T`). -/
noncomputable def MDP.trajProb (M : MDP S) (s₀ : S) (δ : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : ℝ :=
  (if x 0 = s₀ then 1 else 0) *
    ∏ t : Fin T, M.p (x t.castSucc) (δ (x t.castSucc) (t : ℕ)) (t : ℕ) (x t.succ)

/-- The finite-horizon cost `∑_{t=0}^{T} c(s_t, δ(s_t, t), t)` along a trajectory. -/
noncomputable def MDP.trajCost (M : MDP S) (δ : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : ℝ :=
  ∑ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ)

/-- The expectation of the finite-horizon cost `∑_{t=0}^{T} c(s_t, δ(s_t, t), t)` under `δ`
from `s₀`, written as a sum over trajectories. -/
noncomputable def MDP.expCost (M : MDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) : ℝ :=
  ∑ x : Fin (T + 1) → S, M.trajProb s₀ δ T x * M.trajCost δ T x

/-- The optimal finite-horizon expected cost: the infimum over all policies `δ(s, t)`. -/
noncomputable def MDP.optCost (M : MDP S) (s₀ : S) (T : ℕ) : ℝ :=
  ⨅ δ : M.Policy, M.expCost s₀ δ T

/-- The expected cost incurred at time `t`, `E[c(s_t, δ(s_t, t), t)]`, under `δ` from `s₀`. -/
noncomputable def MDP.expCostAt (M : MDP S) (s₀ : S) (δ : M.Policy) (t : ℕ) : ℝ :=
  ∑ x : Fin (t + 1) → S,
    M.trajProb s₀ δ t x * M.c (x (Fin.last t)) (δ (x (Fin.last t)) t) t

/-- The expected discounted cost `∑_{t=0}^{∞} β^t E[c(s_t, δ(s_t, t), t)]` (a `tsum`, which is
`0` if the series is not summable; it is summable whenever the costs are bounded and
`0 ≤ β < 1`). -/
noncomputable def MDP.discCost (M : MDP S) (s₀ : S) (δ : M.Policy) (β : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * M.expCostAt s₀ δ t

/-- The optimal expected discounted cost: the infimum over all policies `δ(s, t)`. -/
noncomputable def MDP.optDiscCost (M : MDP S) (s₀ : S) (β : ℝ) : ℝ :=
  ⨅ δ : M.Policy, M.discCost s₀ δ β

end MDPComplexity.CircuitValue
