import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDepTrials.MixSqrt

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

/-- `W = Σ_{i=1}^n X_i` (§2, p. 535). -/
def W {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω => ∑ i ∈ Finset.Icc 1 n, X i ω

/-- `V^{(i)} = Σ_{|k − i| > m} X_k` (§2, p. 535). -/
def V {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) : Ω → ℕ :=
  fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => m < Int.natAbs ((k : ℤ) - i)), X k ω

/-- `Y_{i t} = V^{(i)} + Σ_{k=i−m}^{t} X_k` (pp. 535–536), with an integer upper index `t`;
the sum is empty when `t < i − m`. -/
def Y {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) : Ω → ℕ :=
  fun ω => V n m X i ω +
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ t), X k ω

/-- `Y'_{i t} = V^{(i)} + Σ_{k=i−m, k≠i}^{t} X_k` (p. 536). -/
def Y' {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) : Ω → ℕ :=
  fun ω => V n m X i ω +
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i ∧ (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ t),
      X k ω

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

/-- `ℳ_{a,b} = ℬ(X_i : a ≤ i ≤ b)` (§4, p. 538). -/
def sigmaIcc {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a b : ℕ) :
    MeasurableSpace Ω :=
  ⨆ i ∈ Finset.Icc a b, MeasurableSpace.comap (X i) inferInstance

/-- `ℳ_{a,∞} = ℬ(X_i : i ≥ a)` (§4, p. 538). -/
def sigmaIci {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a : ℕ) :
    MeasurableSpace Ω :=
  ⨆ i ∈ Set.Ici a, MeasurableSpace.comap (X i) inferInstance

/-- Ibragimov's mixing condition (4.1), p. 538: `φ` is nonincreasing with `φ(k) → 0`, and for all
`j, k ≥ 1` and every `B ∈ ℳ_{j+k,∞}`, `|P(B | ℳ_{1j}) − P(B)| ≤ φ(k)` almost surely. -/
def IbragimovMixing {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (X : ℕ → Ω → β) (φ : ℕ → ℝ) : Prop :=
  Antitone φ ∧ Tendsto φ atTop (𝓝 0) ∧
    ∀ j k : ℕ, 1 ≤ j → 1 ≤ k → ∀ B : Set Ω, MeasurableSet[sigmaIci X (j + k)] B →
      ∀ᵐ ω ∂P, |(P[B.indicator (fun _ => (1 : ℝ)) | sigmaIcc X 1 j]) ω - P.real B| ≤ φ k

/-- m-dependence (p. 538): `(X_1, …, X_r)` and `(X_{r+k}, X_{r+k+1}, …)` are independent whenever
`k > m`. -/
def IsMDependent {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (X : ℕ → Ω → β) (m : ℕ) : Prop :=
  ∀ r k : ℕ, m < k → Indep (sigmaIcc X 1 r) (sigmaIci X (r + k)) P

end PoissonDepTrials.MixSqrt
