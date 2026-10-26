import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel

namespace RegretBandits.Stochastic

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta

/-- The stochastic bandit with `K` arms of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, Ch. 2,
p. 8, and the protocol box of p. 4), in the "stack of rewards" representation: `X i k ω` is the
reward the forecaster receives at the `(k + 1)`-st pull of arm `i` (`k = 0, 1, 2, …`).
The family `(X i k)_{i, k}` is mutually independent, the rewards of one arm are identically
distributed, and `μ i` is the mean of arm `i`. Every forecaster induces the same joint law of
arms and rewards in this representation as in the book's protocol (the reward of a round is drawn
from `ν_{I_t}` independently of the past). -/
structure IsStochasticBandit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) : Prop where
  measurable : ∀ i k, Measurable (X i k)
  indep : iIndepFun (fun p : Fin K × ℕ => X p.1 p.2) P
  identDistrib : ∀ i k, IdentDistrib (X i k) (X i 0) P P
  integrable : ∀ i, Integrable (X i 0) P
  mean : ∀ i, ∫ ω, X i 0 ω ∂P = μ i

/-- The moment condition (2.2) of Bubeck and Cesa-Bianchi (p. 10) for a real random variable `Y`
with mean `m`: for every `λ ≥ 0` the moment generating functions of `Y - m` and `m - Y` at `λ` are
finite and `ln 𝔼 e^{λ(Y - 𝔼Y)} ≤ ψ(λ)`, `ln 𝔼 e^{λ(𝔼Y - Y)} ≤ ψ(λ)`. Finiteness is written as
integrability of the exponential (otherwise Lean's integral would be the junk value `0`). -/
def MomentCondition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ψ : ℝ → ℝ)
    (Y : Ω → ℝ) (m : ℝ) : Prop :=
  ∀ l : ℝ, 0 ≤ l →
    Integrable (fun ω => Real.exp (l * (Y ω - m))) P ∧
    Real.log (∫ ω, Real.exp (l * (Y ω - m)) ∂P) ≤ ψ l ∧
    Integrable (fun ω => Real.exp (l * (m - Y ω))) P ∧
    Real.log (∫ ω, Real.exp (l * (m - Y ω)) ∂P) ≤ ψ l

/-- The standing assumption (2.2) of Section 2.2 for a whole bandit: `ψ` is convex on the reals
and every arm's reward distribution satisfies the moment condition with this same `ψ`. -/
def SatisfiesMomentCondition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (ψ : ℝ → ℝ) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) : Prop :=
  ConvexOn ℝ Set.univ ψ ∧ ∀ i, MomentCondition P ψ (X i 0) (μ i)

/-- The Legendre–Fenchel transform `ψ*(ε) = sup_{λ ∈ ℝ} (λε - ψ(λ))` (p. 10), valued in the
extended reals, so that `ψ*(ε) = +∞` is represented faithfully. -/
noncomputable def legendreFenchel (ψ : ℝ → ℝ) (ε : ℝ) : EReal :=
  ⨆ l : ℝ, ((l * ε - ψ l : ℝ) : EReal)

/-- The generalized inverse `(ψ*)⁻¹(y) = inf {ε ≥ 0 : ψ*(ε) ≥ y}` used in the (α, ψ)-UCB index
(p. 10). For real-valued `ψ` the set is nonempty (`ψ*(ε) ≥ ε - ψ(1) → ∞`) and bounded below by
`0`, so the real infimum is a genuine infimum. -/
noncomputable def lfInv (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ (y : EReal) ≤ legendreFenchel ψ ε}

/-- `μ̂_{i,s}`, the sample mean of the first `s` rewards obtained from arm `i` (p. 10):
`(1/s) ∑_{k < s} X i k`. At `s = 0` Lean returns the junk value `0`; it is never used there. -/
noncomputable def sampleMean {Ω : Type*} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (i : Fin K) (s : ℕ)
    (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range s, X i k ω) / (s : ℝ)

/-- The pseudo-regret (2.1), p. 8: `R̄_n = n μ* - 𝔼 ∑_{t=1}^n μ_{I_t}`, where round `t + 1` plays
arm `I (t + 1) ω` (the value `I 0` is never used) and `μ* = bestMean μ = max_i μ_i`. -/
noncomputable def pseudoRegretBar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K) (n : ℕ) : ℝ :=
  (n : ℝ) * bestMean μ - ∫ ω, ∑ t ∈ Finset.range n, μ (I (t + 1) ω) ∂P

end RegretBandits.Stochastic
