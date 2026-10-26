import Mathlib

namespace StoneRegression.Criterion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- A sequence of weight functions: `W n x xs i = W_{n,i+1}(x, x₁, …, xₙ)` (p. 596), with the sample
`xs i = x_{i+1}` 0-based. Weights with index `> n` are `0` in the paper and do not exist here. -/
abbrev WeightSeq (d : ℕ) : Type :=
  (n : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin n → EuclideanSpace ℝ (Fin d)) → Fin n → ℝ

/-- Each `W n` is jointly Borel in `(x, x₁, …, xₙ)` (standing assumption, disclosed). -/
def MeasurableWeights {d : ℕ} (W : WeightSeq d) : Prop :=
  ∀ n, Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n p.1 p.2)

/-- `W_n ≥ 0` for every `n` (p. 596, "nonnegative"). -/
def Nonneg {d : ℕ} (W : WeightSeq d) : Prop := ∀ n x xs i, 0 ≤ W n x xs i

/-- Probability weights (p. 596): nonnegative and `∑ᵢ W_{ni}(x) = 1`, for every `n ≥ 1`. -/
def ProbWeights {d : ℕ} (W : WeightSeq d) : Prop :=
  ∀ n, 1 ≤ n → ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1

/-- The law of the i.i.d. sequence `X, X₁, X₂, …` on `ℕ → ℝᵈ`: coordinate `0` is `X`, coordinate `i+1` is
`X_{i+1}` (p. 596). -/
noncomputable def xLaw {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    Measure (ℕ → EuclideanSpace ℝ (Fin d)) :=
  Measure.infinitePi (fun _ : ℕ => μ)

/-- The first `n` sample points `(X₁, …, Xₙ)` of a path, 0-based. -/
def sample {α : Type*} (ω : ℕ → α) (n : ℕ) : Fin n → α := fun i => ω (i.val + 1)

/-- `W_{n,i+1}(X)` on the path `ω` of the `X`-sequence. -/
def wAt {d : ℕ} (W : WeightSeq d) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℝ :=
  W n (ω 0) (sample ω n) i

/-- The law of the i.i.d. pairs `(X, Y), (X₁, Y₁), …` when `X ~ μ` and `κ` is the conditional law of `Y`
given `X`. -/
noncomputable def pairLaw {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    Measure (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => μ ⊗ₘ κ)

/-- The estimate `Ê_n(Y | X) = ∑ᵢ W_{ni}(X) Yᵢ` (p. 596) on a path of pairs. -/
def estimate {d : ℕ} (W : WeightSeq d) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i * (ω (i.val + 1)).2

/-- The regression function `E(Y | X = x) = ∫ y κ(x, dy)`. -/
noncomputable def regFn {d : ℕ} (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, y ∂(κ x)

/-- Consistency (p. 597): for every conditional law `κ` of `Y` given `X` and every `r > 1` with
`E|Y|ʳ < ∞`, `E|Ê_n(Y|X) − E(Y|X)|ʳ → 0`. -/
def IsConsistent {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) : Prop :=
  ∀ (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] (r : ℝ), 1 < r →
    ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞ →
    Tendsto (fun n => ∫⁻ ω, ‖estimate W n ω - regFn κ (ω 0).1‖ₑ ^ r ∂(pairLaw μ κ)) atTop (𝓝 0)

/-- Condition (1) with constant `C` (p. 598): `E ∑ᵢ |W_{ni}(X)| f(Xᵢ) ≤ C·E f(X)` for every nonnegative
Borel `f` and every `n ≥ 1`. -/
def Cond1 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d)
    (C : ℝ≥0) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∀ n, 1 ≤ n →
    ∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) ≤ C * ∫⁻ x, f x ∂μ

/-- Condition (2) with constant `D` (p. 598): `P(∑ᵢ |W_{ni}(X)| ≤ D) = 1` for every `n ≥ 1`. -/
def Cond2 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d)
    (D : ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ᵐ ω ∂(xLaw μ), ∑ i : Fin n, |wAt W n ω i| ≤ D

/-- Condition (3) (p. 598): `∑ᵢ |W_{ni}(X)| I{‖Xᵢ − X‖ > a} → 0` in probability for every `a > 0`. -/
def Cond3 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d) : Prop :=
  ∀ a : ℝ, 0 < a → TendstoInMeasure (xLaw μ)
    (fun n ω => ∑ i : Fin n, |wAt W n ω i| * (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0)) atTop (fun _ => 0)

/-- Condition (4) (p. 598): `∑ᵢ W_{ni}(X) → 1` in probability. -/
def Cond4 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d) : Prop :=
  TendstoInMeasure (xLaw μ) (fun n ω => ∑ i : Fin n, wAt W n ω i) atTop (fun _ => 1)

/-- Condition (5) (p. 598): `maxᵢ |W_{ni}(X)| → 0` in probability. The `⨆` over `Fin n` is the true maximum
for `n ≥ 1` (finite, nonempty) and `0` for `n = 0`. -/
def Cond5 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d) : Prop :=
  TendstoInMeasure (xLaw μ) (fun n ω => ⨆ i : Fin n, |wAt W n ω i|) atTop (fun _ => 0)

end StoneRegression.Criterion
