import Mathlib

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- The interarrival-time law of the G/M/1 queue (§5.3.1, p.259): a probability measure `A` on `ℝ`
(the law of the interarrival time `T`, with CDF `A(t)`), carried by `[0, ∞)`, with finite mean
`E[T] = 1/λ`. -/
structure IsInterarrivalLaw (A : Measure ℝ) (lam : ℝ) : Prop where
  isProbability : IsProbabilityMeasure A
  nonneg : A (Set.Iio 0) = 0
  integrable : Integrable (fun x : ℝ => x) A
  mean : ∫ x, x ∂A = 1 / lam

/-- Eq. (5.50): `b_k = ∫_0^∞ e^{-μt} (μt)^k / k! dA(t)`, the probability of exactly `k` exponential
(rate `μ`) service completions during an interarrival time. -/
noncomputable def serviceProb (A : Measure ℝ) (mu : ℝ) (k : ℕ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), Real.exp (-mu * t) * (mu * t) ^ k / (Nat.factorial k : ℝ) ∂A

/-- Eq. (5.51): the one-step transition probabilities `p_{ij}` of the arrival-point chain
`X_{n+1} = X_n + 1 - B_n`:
`p_{i0} = 1 - ∑_{k=0}^{i} b_k`, `p_{ij} = b_{i+1-j}` for `1 ≤ j ≤ i + 1`, and `p_{ij} = 0` for
`j > i + 1`. -/
noncomputable def transitionProb (A : Measure ℝ) (mu : ℝ) (i j : ℕ) : ℝ :=
  if j = 0 then 1 - ∑ k ∈ Finset.range (i + 1), serviceProb A mu k
  else if j ≤ i + 1 then serviceProb A mu (i + 1 - j)
  else 0

/-- Eq. (5.52): `q = {q_n}` is a stationary probability vector of the arrival-point chain, i.e.
`q ≥ 0`, `qe = 1` and `qP = q` (each `(qP)_j = ∑_i q_i p_{ij}` a convergent series equal to `q_j`). -/
def IsArrivalPointStationary (A : Measure ℝ) (mu : ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ q n) ∧ HasSum q 1 ∧
    ∀ j, HasSum (fun i => q i * transitionProb A mu i j) (q j)

/-- Eq. (5.55): the probability generating function `β(z) = ∑_{n ≥ 0} b_n z^n` of `{b_n}`, at a
complex argument `z`. -/
noncomputable def beta (A : Measure ℝ) (mu : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (serviceProb A mu n : ℂ) * z ^ n

/-- The Laplace–Stieltjes transform `A*(s) = ∫_0^∞ e^{-sx} dA(x)` of the interarrival-time CDF, at a
complex argument `s`. -/
noncomputable def lst (A : Measure ℝ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ici (0 : ℝ), Complex.exp (-s * (x : ℂ)) ∂A

end QueueingFundamentals.GM1
