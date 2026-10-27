import Mathlib

namespace TailOptCaching.ETLRU

open MeasureTheory
open scoped ENNReal

/-- Standing parameters of the stochastic conversation model (Zhang–Li–Moallemi–Peng,
arXiv:2510.15152v1, §5, p. 8): cache capacity `C` (blocks), tail threshold `ξ ≥ 0`, birth rate
`lamConv > 0` of new conversations, return rates `lamBar i > 0` of active conversations, the known
law `Qlaw i` of the prompt length of conversation `i`, the (arbitrary) law `Alaw i` of its response
length, and the law `decayLaw r` of the decay factor `d = exp(−μτ)` over the next inter-arrival
time `τ` when the belief rate vector is `r` (any probability law on `(0, 1]`). -/
structure Params where
  C : ℕ
  ξ : ℝ
  ξ_nonneg : 0 ≤ ξ
  lamConv : ℝ
  lamConv_pos : 0 < lamConv
  lamBar : ℕ → ℝ
  lamBar_pos : ∀ i, 0 < lamBar i
  Qlaw : ℕ → PMF ℕ
  Alaw : ℕ → PMF ℕ
  decayLaw : (ℕ → ℝ) → Measure ℝ
  decayLaw_prob : ∀ r, IsProbabilityMeasure (decayLaw r)
  decayLaw_mem : ∀ r, decayLaw r (Set.Ioc (0 : ℝ) 1)ᶜ = 0

/-- Belief state `(λ, L, X)`: conversations `0, …, n − 1` have arrived; `lam i` is the belief
turn-arrival rate, `L i` the conversation length (blocks), `X i` the number of cached blocks. -/
structure State where
  n : ℕ
  lam : ℕ → ℝ
  L : ℕ → ℕ
  X : ℕ → ℕ

/-- Reachable-type states: `0 < λ_i ≤ λ̄_i` for arrived conversations, nothing beyond `n`,
`X_i ≤ L_i`, and the cache respects the capacity. -/
def WellFormed (P : Params) (s : State) : Prop :=
  (∀ i < s.n, 0 < s.lam i ∧ s.lam i ≤ P.lamBar i) ∧
  (∀ i, s.n ≤ i → s.lam i = 0 ∧ s.L i = 0 ∧ s.X i = 0) ∧
  (∀ i, s.X i ≤ s.L i) ∧
  ∑ i ∈ Finset.range s.n, s.X i ≤ P.C

/-- `Φ(λ, τ)`: every belief rate multiplied by the decay factor `d = exp(−μτ)`. -/
def decay (d : ℝ) (s : State) : State := { s with lam := fun i => d * s.lam i }

/-- Probability that the next arrival is conversation `θ` (from an already decayed state): an
existing `θ < n` with probability `λ_θ / (λ_conv + Σ_i λ_i)`, a new conversation `θ = n` with
probability `λ_conv / (λ_conv + Σ_i λ_i)`. -/
noncomputable def arrivalProb (P : Params) (s : State) (θ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((if θ < s.n then s.lam θ else if θ = s.n then P.lamConv else 0) /
    (P.lamConv + ∑ i ∈ Finset.range s.n, s.lam i))

/-- Expectation over the next arrival `θ′`, its prompt length `Q′ ∼ Qlaw θ′` and its response
length `A′ ∼ Alaw θ′`. -/
noncomputable def arrivalExp (P : Params) (s : State) (F : ℕ → ℕ → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ θ ∈ Finset.range (s.n + 1), arrivalProb P s θ *
    ∑' q : ℕ, P.Qlaw θ q * ∑' a : ℕ, P.Alaw θ a * F θ q a

/-- Number of arrived conversations after conversation `θ` arrives (`dim(X, θ)`). -/
def nAfter (s : State) (θ : ℕ) : ℕ := max s.n (θ + 1)

/-- Post-decision state: `Γ` (`λ_θ ← λ̄_θ`), `Ψ` (`L_θ ← L_θ + Q + A`), cache vector `Y`. -/
def post (P : Params) (s : State) (θ q a : ℕ) (Y : ℕ → ℕ) : State :=
  { n := nAfter s θ
    lam := Function.update s.lam θ (P.lamBar θ)
    L := Function.update s.L θ (s.L θ + q + a)
    X := Y }

/-- Feasible caching decisions: (9) optional caching, (10) cannot conjure caches, and the
capacity constraint. -/
def Feasible (P : Params) (s : State) (θ q a : ℕ) (Y : ℕ → ℕ) : Prop :=
  Y θ ≤ s.L θ + q + a ∧ (∀ i, i ≠ θ → Y i ≤ s.X i) ∧
  ∑ i ∈ Finset.range (nAfter s θ), Y i ≤ P.C

/-- Tail Excess Latency of the arrival of `θ` with prompt `q`: `(L_θ + Q − X_θ − ξ)^+`. -/
noncomputable def stageCost (P : Params) (s : State) (θ q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((s.L θ : ℝ) + q - s.X θ - P.ξ)

/-- Objective of (8) at a post-decision state `z`:
`Σ_i λ_i · E[(L_i + Q_i − X_i − ξ)^+]`, `Q_i ∼ Qlaw i`. -/
noncomputable def nextTEL (P : Params) (z : State) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range z.n, ENNReal.ofReal (z.lam i) *
    ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((z.L i : ℝ) + Q - z.X i - P.ξ)

/-- A Markov deterministic caching policy: (stage, belief state, arriving conversation, prompt
length, response length) ↦ cache vector after service. -/
abbrev Policy := ℕ → State → ℕ → ℕ → ℕ → (ℕ → ℕ)

/-- Every decision of the policy is feasible. -/
def Admissible (P : Params) (π : Policy) : Prop :=
  ∀ k s θ q a, θ ≤ s.n → Feasible P s θ q a (π k s θ q a)

/-- Definition 1 (ET-LRU): every decision is a feasible minimizer of (8) subject to (9), (10)
and the capacity constraint (any tie-break). -/
def IsETLRU (P : Params) (σ : Policy) : Prop :=
  ∀ k s θ q a, θ ≤ s.n → Feasible P s θ q a (σ k s θ q a) ∧
    ∀ Y, Feasible P s θ q a Y →
      nextTEL P (post P s θ q a (σ k s θ q a)) ≤ nextTEL P (post P s θ q a Y)

/-- Expected total TEL of the next `r` arrivals under `π`, from the state `z` just after the last
decision (before the decay); `k` is the stage index fed to `π`. -/
noncomputable def value (P : Params) (π : Policy) : ℕ → ℕ → State → ℝ≥0∞
  | 0, _, _ => 0
  | r + 1, k, z => ∫⁻ d, arrivalExp P (decay d z) (fun θ q a =>
        stageCost P (decay d z) θ q +
        value P π r (k + 1) (post P (decay d z) θ q a (π k (decay d z) θ q a)))
      ∂(P.decayLaw z.lam)

/-- The finite-horizon Bellman optimum of App. B (the minimum over the feasible set taken as an
infimum), `r` arrivals remaining. -/
noncomputable def optValue (P : Params) : ℕ → State → ℝ≥0∞
  | 0, _ => 0
  | r + 1, z => ∫⁻ d, arrivalExp P (decay d z) (fun θ q a =>
        stageCost P (decay d z) θ q +
        ⨅ (Y : ℕ → ℕ) (_ : Feasible P (decay d z) θ q a Y),
          optValue P r (post P (decay d z) θ q a Y))
      ∂(P.decayLaw z.lam)

/-- `P(L + Q_i − ξ ≥ X)` for conversation `i`. -/
noncomputable def tailProb (P : Params) (i L X : ℕ) : ℝ≥0∞ :=
  ∑' Q : ℕ, if (X : ℝ) ≤ (L : ℝ) + Q - P.ξ then P.Qlaw i Q else 0

/-- Ranking criterion `λ_i · P(L_i + Q_i − ξ ≥ X_i)` at a post-decision state. -/
noncomputable def score (P : Params) (z : State) (i : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (z.lam i) * tailProb P i (z.L i) (z.X i)

/-- Evict one cached token of conversation `j`. -/
def evict (z : State) (j : ℕ) : State := { z with X := Function.update z.X j (z.X j - 1) }

/-- One pass of the while loop of Algorithm 2: evict one token from a conversation `j < n` with
`X_j ≥ 1` of minimal score (any tie-break). -/
def GreedyStep (P : Params) (z z' : State) : Prop :=
  ∃ j < z.n, 1 ≤ z.X j ∧ (∀ i < z.n, 1 ≤ z.X i → score P z j ≤ score P z i) ∧ z' = evict z j

/-- `m` passes of the while loop of Algorithm 2. -/
def GreedyRun (P : Params) : ℕ → State → State → Prop
  | 0, z, z' => z' = z
  | m + 1, z, z' => ∃ z'', GreedyStep P z z'' ∧ GreedyRun P m z'' z'

end TailOptCaching.ETLRU
