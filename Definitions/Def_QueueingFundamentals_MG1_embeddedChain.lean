import Mathlib

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- `k_i = ∫_0^∞ e^{-λt}(λt)^i / i! dB(t)` (Eq. (5.9), p.226): the probability of `i` Poisson(`λ`)
arrivals during a service time with distribution `B`. The service distribution `B` is a measure on
`ℝ`; the theorems assume it is a probability measure concentrated on `[0, ∞)`. The arrival rate is
written `lam` because `λ` is a Lean keyword. -/
noncomputable def arrivalProb (lam : ℝ) (B : Measure ℝ) (i : ℕ) : ℝ :=
  ∫ t, Real.exp (-(lam * t)) * (lam * t) ^ i / (Nat.factorial i : ℝ) ∂B

/-- The transition matrix (5.10) (p.227) of the M/G/1 departure-point chain on `ℕ`:
row `0` is `(k_0, k_1, k_2, …)`, and for `i ≥ 1`, `p_{ij} = k_{j-i+1}` when `j ≥ i - 1` and `0`
otherwise. The index `j + 1 - i` is only used when `i ≤ j + 1`, so no natural-number subtraction
is truncated. -/
noncomputable def transitionMatrix (lam : ℝ) (B : Measure ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then arrivalProb lam B j
  else if i ≤ j + 1 then arrivalProb lam B (j + 1 - i) else 0

/-- `π` is a stationary probability vector of the transition matrix `P` on `ℕ`: its entries are
nonnegative, sum to `1`, and satisfy `πP = π` (Eq. (5.11), p.227), i.e.
`∑_i π_i p_{ij} = π_j` for every `j`. -/
def IsStationaryDist (P : ℕ → ℕ → ℝ) (π : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧ ∀ j, HasSum (fun i => π i * P i j) (π j)

/-- The generating function `∑_{i ≥ 0} a_i z^i` of a real sequence `a` at a complex argument `z`
(Eq. (5.13), p.227, for `|z| ≤ 1`). `Π(z) = pgf π z` and `K(z) = pgf (arrivalProb lam B) z`. -/
noncomputable def pgf (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' i, (a i : ℂ) * z ^ i

/-- The mean service time `E[S] = ∫ t dB(t)`. -/
noncomputable def meanService (B : Measure ℝ) : ℝ :=
  ∫ t, t ∂B

/-- The service-time variance `σ_B² = E[S²] - E²[S]`. -/
noncomputable def serviceVariance (B : Measure ℝ) : ℝ :=
  (∫ t, t ^ 2 ∂B) - (meanService B) ^ 2

/-- The traffic intensity `ρ = λ E[S]` (Eq. (5.15), p.227; `ρ = λ/μ` with `μ = 1/E[S]`, p.219). -/
noncomputable def utilization (lam : ℝ) (B : Measure ℝ) : ℝ :=
  lam * meanService B

end QueueingFundamentals.MG1
