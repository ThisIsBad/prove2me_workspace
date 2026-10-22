import Mathlib

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

/-- The Poisson weight $e^{-\lambda t}(\lambda t)^k/k!$. -/
noncomputable def poisW (lam t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(lam * t)) * (lam * t) ^ k / (k.factorial : ℝ)

/-- (2.1): $\bar H(t) = \sum_k \bar P_k e^{-\lambda t}(\lambda t)^k/k!$ for $t \ge 0$,
and $\bar H(t) = 1$ for $t < 0$. -/
noncomputable def shockSurv (lam : ℝ) (P : ℕ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then 1 else ∑' k, P k * poisW lam t k

/-- The k-fold convolution $F^{(k)}$ of a law on ℝ; $F^{(0)}$ is degenerate at 0 (p. 636). -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => Measure.conv (convPow μ k) μ

/-- $F^{(k)}(x)$ = the mass of $(-\infty, x]$ under the k-fold convolution. -/
noncomputable def cdfPow (μ : Measure ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (convPow μ k (Set.Iic x)).toReal

/-- The survival function $\bar G(x) = 1 - G(x) = \nu((x, \infty))$ of a law `ν` on ℝ. -/
noncomputable def survOf (ν : Measure ℝ) (x : ℝ) : ℝ :=
  (ν (Set.Ioi x)).toReal

/-- (5.1): $\bar P_k = \int_0^\infty F^{(k)}(x)\, dG(x)$, the integral taken over ℝ
(the threshold law `ν` is carried by $[0, \infty)$ in every statement that uses it). -/
noncomputable def randP (μ ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, cdfPow μ k x ∂ν

/-- (ii) IHR: $\bar F(x + t)/\bar F(t)$ is decreasing (non-increasing) in $t$ whenever $x > 0$,
cross-multiplied. -/
def IsIHR (Fb : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, s ≤ t → Fb (x + t) * Fb s ≤ Fb (x + s) * Fb t

/-- (iv) IHRA: $[\bar F(t)]^{1/t}$ is decreasing (non-increasing) in $t > 0$ (real power). -/
def IsIHRA (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => Fb t ^ (1 / t)) (Set.Ioi 0)

/-- (v) NBU: $\bar F(x) \ge \bar F(t + x)/\bar F(t)$ for all $x, t \ge 0$, cross-multiplied. -/
def IsNBU (Fb : ℝ → ℝ) : Prop :=
  ∀ x t, 0 ≤ x → 0 ≤ t → Fb (t + x) ≤ Fb x * Fb t

end ShockWear.RandThreshold
