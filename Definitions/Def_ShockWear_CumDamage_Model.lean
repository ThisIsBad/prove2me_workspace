import Mathlib

namespace ShockWear.CumDamage

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

/-- $F^{(k)}(x) = $ the mass of $(-\infty, x]$ under the k-fold convolution. -/
noncomputable def cdfPow (μ : Measure ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (convPow μ k (Set.Iic x)).toReal

/-- $F_1 * \cdots * F_k$ for a sequence of laws, with the paper's $F_i$ = `μ (i - 1)`;
the empty convolution (k = 0) is degenerate at 0. -/
noncomputable def convProdPow (μ : ℕ → Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => Measure.conv (convProdPow μ k) (μ k)

/-- (iv) IHRA: $[\bar F(t)]^{1/t}$ is decreasing (non-increasing) in $t > 0$ (real power). -/
def IsIHRA (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => Fb t ^ (1 / t)) (Set.Ioi 0)

/-- `g` has at most one sign change on `D`, from + to − if one occurs. -/
def SignPM (g : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ s ∈ D, ∀ t ∈ D, s < t → ¬ (g s < 0 ∧ 0 < g t)

/-- A sequence has at most one sign change, from + to − if one occurs. -/
def SignPMSeq (a : ℕ → ℝ) : Prop :=
  ∀ j k, j < k → ¬ (a j < 0 ∧ 0 < a k)

/-- The number $N(x)$ of renewals in $[0, x]$, not counting the origin:
the number of $k \ge 1$ with $X_1 + \cdots + X_k \le x$ (paper's $X_i$ = Lean `X (i - 1)`),
as an extended natural number. -/
noncomputable def renewalCount {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (ω : Ω) : ℕ∞ :=
  {k : ℕ | 1 ≤ k ∧ ∑ i ∈ Finset.range k, X i ω ≤ x}.encard

end ShockWear.CumDamage
