import Mathlib

open MeasureTheory ProbabilityTheory

namespace SolomonRWRE.DiffEq

/-- **The system of difference equations (4.1).**
Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975),
DOI 10.1214/aop/1176996444, p. 28, display (4.1):
`Z_0 = 0`, `Z_n = σ_n (1 + Z_{n−1})` for `n ≥ 1`.

`Z σ n ω` is defined by this recursion, so the recursion is not a hypothesis.

**Formalization Note.** `Z_n` uses only `σ_1, …, σ_n`; the value `σ 0` never enters. -/
def Z {Ω : Type*} (σ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => σ (n + 1) ω * (1 + Z σ n ω)

/-- **The driving sequence of (4.1).** p. 28: "`{σ_n}` is a sequence of independent,
identically distributed nonnegative random variables".

**Formalization Note.** The sequence used by (4.1) is `σ_1, σ_2, …`; the hypotheses are put
on the shifted family `n ↦ σ (n + 1)`, so `σ 0` (unused) is unconstrained. Nonnegativity is
pointwise (the convention of the series). -/
structure IsIIDNonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ : ℕ → Ω → ℝ) :
    Prop where
  meas : ∀ n, Measurable (σ (n + 1))
  nonneg : ∀ n ω, 0 ≤ σ (n + 1) ω
  indep : iIndepFun (fun n => σ (n + 1)) P
  ident : ∀ n, IdentDistrib (σ (n + 1)) (σ 1) P P

/-- **`ν = E(σ)`** (Theorem (4.4), p. 28), the expectation of the common law, as a lower
Lebesgue integral in `[0, ∞]`.

**Formalization Note.** `σ` need not be integrable, so `ν = ∞` is possible; a Bochner integral
would return the junk value `0` in that case. -/
noncomputable def nu {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ : ℕ → Ω → ℝ) :
    ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (σ 1 ω) ∂P

/-- **`Y_k^n`** (proof of Theorem (4.4), p. 28):
`Y_k^n = Σ_{j=1}^{n−k+1} Π_{i=j}^{j+k−1} σ_i`, the sum of the products of `k` consecutive
`σ`'s inside `σ_1, …, σ_n`.

**Formalization Note.** Natural-number subtraction: for `n < k` the range `Icc 1 (n + 1 - k)`
is empty and `Y_k^n = 0`, which is the page's empty sum. Only `k ≥ 1` is used. -/
def Y {Ω : Type*} (σ : ℕ → Ω → ℝ) (k n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n + 1 - k), ∏ i ∈ Finset.Icc j (j + k - 1), σ i ω

/-- **`ρ_j = σ_1 ⋯ σ_j`** (Lemma (4.2)(i), p. 28). -/
def rho {Ω : Type*} (σ : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.Icc 1 j, σ i ω

/-- Expectation of the positive part of `ln σ_1`, in `[0, ∞]`; `ln 0 = −∞`. -/
noncomputable def logPosMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (σ : ℕ → Ω → ℝ) : ENNReal :=
  ∫⁻ ω, (ENNReal.log (ENNReal.ofReal (σ 1 ω))).toENNReal ∂P

/-- Expectation of the negative part of `ln σ_1`, in `[0, ∞]`; `ln 0 = −∞`. -/
noncomputable def logNegMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (σ : ℕ → Ω → ℝ) : ENNReal :=
  ∫⁻ ω, (-ENNReal.log (ENNReal.ofReal (σ 1 ω))).toENNReal ∂P

/-- "`E(ln σ)` is defined (possibly infinite)" (Lemma (4.2), p. 28): the positive and the
negative part of `ln σ` do not both have infinite expectation. -/
def LogMeanDefined {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ : ℕ → Ω → ℝ) : Prop :=
  logPosMean P σ ≠ ⊤ ∨ logNegMean P σ ≠ ⊤

/-- **`E(ln σ)`** in `[−∞, ∞]`, the difference of the expectations of the positive and the
negative part. Meaningful only under `LogMeanDefined` (otherwise it is `⊤ − ⊤`). -/
noncomputable def logMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (σ : ℕ → Ω → ℝ) : EReal :=
  (logPosMean P σ : EReal) - (logNegMean P σ : EReal)

end SolomonRWRE.DiffEq
