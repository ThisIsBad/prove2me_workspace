import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
Chapter 2 (pp. 19-53): main ideas, the Gittins index.

The discrete-time setting of §2.4-2.6 (p. 23): a bandit process `B` is a Markov reward process on
a countable state space `E` with transition probabilities `P(y | x)`, a bounded reward `r(x)`
collected each time the continuation control is applied, and a discount factor `a ∈ (0,1)`. This
is exactly the single-arm model of the live *Bandit Algorithms* series (`Def_GittinsIndex`, L&S
§35.4): `markovChainMeasure P x` is the law of the process started at `x`, a stopping time is a
`Kernel`-trajectory stopping time (`IsTrajStoppingTime`), and `gittinsIndex P r a x` is the
index (2.6), `ν(B, x) = sup_{τ > 0} R_τ(B, x) / W_τ(B, x)`. Nothing of that model is restated
here; this module names the book's quantities on top of it.

* `stoppedReward P r a τ x = R_τ(B, x) = E[∑_{t<τ} a^t r(x(t)) | x(0) = x]`,
  `stoppedTime P a τ x = W_τ(B, x) = E[∑_{t<τ} a^t | x(0) = x]`,
  `stoppedRatio P r a τ x = ν_τ(B, x) = R_τ / W_τ` (2.7); `IsPositiveStoppingTime τ` — a
  stopping time taking values in `{1, 2, …} ∪ {∞}` (the book's `τ > 0`).
* `BoundedReward r` — the standing assumption `|r|` bounded (p. 23).
* `hittingTime Σ₀ ω` — the first decision time `t ≥ 1` at which the process is in the stopping
  set `Σ₀` (`∞` if never): the stopping rule with continuation set `Σ₀ᶜ` of Lemma 2.2.
* `fairChargeProfit P r a x λ = sup_{τ>0} E[∑_{t<τ} a^t (r(x(t)) − λ)]`, the maximal expected
  profit when a prevailing charge `λ` is paid per period of continuation (2.5).
* `restartIter P r a ξ k` — the Katehakis–Veinott value iteration of §2.6.4 for the restart-in-
  state problem: `μ_0 = 0`, `μ_{k+1}(x) = max{μ_k(ξ), r(x) + a ∑_y P(y | x) μ_k(y)}`.
* `interchangeValue` — the expected reward from continuing `B₁` for time `τ` and then `B₂` for
  time `σ`, `R_τ(B₁) + E[a^τ] R_σ(B₂)` (Lemma 2.4, p. 34), and `discountAtStop` — `E[a^τ]`.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm

noncomputable section

namespace AllocationIndices

variable {S : Type*} [MeasurableSpace S]

/-- `R_τ(B, x) = E[∑_{t<τ} a^t r(x(t)) | x(0) = x]`, the expected total discounted reward over
`τ` steps (p. 26). -/
def stoppedReward (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ)
    (τ : (ℕ → S) → ℕ∞) (x : S) : ℝ :=
  ∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x

/-- `W_τ(B, x) = E[∑_{t<τ} a^t | x(0) = x] = (1 − a)⁻¹ E[1 − a^τ]`, the expected total discounted
time over `τ` steps (p. 26). -/
def stoppedTime (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (τ : (ℕ → S) → ℕ∞) (x : S) : ℝ :=
  ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x

/-- `ν_τ(B, x) = R_τ(B, x) / W_τ(B, x)`, Eq. (2.7): the equivalent constant reward rate of the
portion of `B` up to `τ`. -/
def stoppedRatio (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ)
    (τ : (ℕ → S) → ℕ∞) (x : S) : ℝ :=
  stoppedReward P r a τ x / stoppedTime P a τ x

/-- A past-measurable stopping time taking values in the decision times `{1, 2, …}` (or `∞`):
the `τ > 0` over which (2.4)-(2.6) take their supremum. -/
def IsPositiveStoppingTime (τ : (ℕ → S) → ℕ∞) : Prop :=
  IsTrajStoppingTime τ ∧ ∀ ω, 1 ≤ τ ω

/-- The standing assumption of §2.4: the reward function is bounded. -/
def BoundedReward (r : S → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x, |r x| ≤ M

/-- `E[a^τ | x(0) = x]`, the expected discount at the stopping time (`a^∞ = 0`). -/
def discountAtStop (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (τ : (ℕ → S) → ℕ∞) (x : S) :
    ℝ :=
  ∫ ω, (match τ ω with
    | (n : ℕ) => a ^ n
    | ⊤ => 0) ∂markovChainMeasure P x

/-- The stopping rule defined by a stopping set `Σ₀` (p. 22): stop at the first decision time
`t ≥ 1` at which the state lies in `Σ₀`, never if there is none. -/
def hittingTime (stopSet : Set S) (ω : ℕ → S) : ℕ∞ :=
  ⨅ t : {t : ℕ // 1 ≤ t ∧ ω t ∈ stopSet}, ((t : ℕ) : ℕ∞)

/-- The maximal expected profit from continuing `B` for one or more periods when a prevailing
charge `λ` is paid at each period of continuation (p. 25, the expression inside (2.5)):
`sup_{τ>0} E[∑_{t<τ} a^t (r(x(t)) − λ) | x(0) = x]`. -/
def fairChargeProfit (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ) (x : S) (lam : ℝ) :
    ℝ :=
  ⨆ τ : {τ : (ℕ → S) → ℕ∞ // IsPositiveStoppingTime τ},
    stoppedReward P r a τ x - lam * stoppedTime P a τ x

/-- The Katehakis–Veinott value iteration for the restart-in-state problem (§2.6.4, p. 31):
`μ_0 = 0` and `μ_{k+1}(x) = max{μ_k(ξ), r(x) + a ∑_y P(y | x) μ_k(y)}`, where `ξ` is the
state in which the bandit may be restarted. -/
def restartIter (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ) (ξ : S) :
    ℕ → S → ℝ
  | 0 => fun _ ↦ 0
  | k + 1 => fun x ↦ max (restartIter P r a ξ k ξ) (r x + a * ∫ y, restartIter P r a ξ k y ∂(P x))

/-- The expected reward from selecting `B₁` (state `x₁`) for time `τ` and then `B₂` (state `x₂`)
for time `σ`, the two processes being independent (Lemma 2.4, p. 34):
`R_τ(B₁) + E[a^τ] R_σ(B₂)`. -/
def interchangeValue {S₁ S₂ : Type*} [MeasurableSpace S₁] [MeasurableSpace S₂]
    (P₁ : Kernel S₁ S₁) [IsMarkovKernel P₁] (r₁ : S₁ → ℝ) (P₂ : Kernel S₂ S₂) [IsMarkovKernel P₂]
    (r₂ : S₂ → ℝ) (a : ℝ) (τ : (ℕ → S₁) → ℕ∞) (σ : (ℕ → S₂) → ℕ∞) (x₁ : S₁) (x₂ : S₂) : ℝ :=
  stoppedReward P₁ r₁ a τ x₁ + discountAtStop P₁ a τ x₁ * stoppedReward P₂ r₂ a σ x₂

end AllocationIndices

end
