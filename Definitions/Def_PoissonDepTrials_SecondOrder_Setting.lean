import Mathlib

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.SecondOrder

/-- Chen (1975), §2, p. 535: `X 1, …, X n` are Bernoulli random variables (values in `{0, 1}`
almost surely), and, following the convention of p. 535, `X i` is identically zero when `i ≤ 0`
or `i ≥ n + 1`. Each `X i` is measurable. -/
def IsBernoulliTrials {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) : Prop :=
  (∀ i, Measurable (X i)) ∧ (∀ i, (i = 0 ∨ n < i) → X i = 0) ∧ ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1

/-- `p_i = P(X_i = 1)` (§2, p. 535). -/
noncomputable def prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ)
    (i : ℕ) : ℝ :=
  P.real {ω | X i ω = 1}

/-- `λ = Σ_{i=1}^n p_i` (§2, p. 535). -/
noncomputable def lam {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, prob P X i

/-- `λ^{(i)} = Σ_{j ≠ i} p_j` (proof of Theorem 5.1, p. 545). -/
noncomputable def lamExcept {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) (i : ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i), prob P X j

/-- `W = Σ_{i=1}^n X_i` (§2, p. 535). -/
def W {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω => ∑ i ∈ Finset.Icc 1 n, X i ω

/-- `W^{(i)} = Σ_{k ≠ i} X_k` (§2, p. 535). -/
def Wi {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) : Ω → ℕ :=
  fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), X k ω

/-- The Poisson expectation `𝒫_λh = e^{−λ} Σ_{k≥0} h(k) λ^k / k!` (2.4), p. 536. -/
noncomputable def poissonExp (lam : ℝ) (h : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * h k

/-- The solution `S_λh(w)` of the Stein equation (2.3), given for `w ≥ 1` by the first line of
(2.5), p. 536: `−(w − 1)! λ^{−w} Σ_{k=0}^{w−1} [h(k) − 𝒫_λh] λ^k / k!`. Its value at `w = 0`
(an empty sum, `0`) plays no role. -/
noncomputable def stein (lam : ℝ) (h : ℕ → ℝ) (w : ℕ) : ℝ :=
  -(((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
    ∑ k ∈ Finset.range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ))

/-- The forward difference `Δf(w) = f(w + 1) − f(w)` (p. 536). -/
def delta (f : ℕ → ℝ) (w : ℕ) : ℝ := f (w + 1) - f w

/-- The shift operator `Lf(w) = f(w + 1)` (§5, p. 543). -/
def shiftL (f : ℕ → ℝ) : ℕ → ℝ := fun w => f (w + 1)

/-- The operator `U_λh(w) = ΔS_λh(w + 1)` (§5, p. 543), defined for every `w ≥ 0`. -/
noncomputable def stU (lam : ℝ) (h : ℕ → ℝ) : ℕ → ℝ :=
  fun w => delta (stein lam h) (w + 1)

end PoissonDepTrials.SecondOrder
