import Mathlib

namespace WorstCaseVaR.Entropy

open MeasureTheory ProbabilityTheory

/-- The return space `ℝⁿ`, as the Euclidean space carrying `multivariateGaussian`. -/
abbrev Returns (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The loss set `𝒮 = {x | γ ≤ -xᵀw}` of Eq. (13): the returns `x` for which the portfolio
`w` loses at least `γ`. -/
def lossSet {n : ℕ} (w : Returns n) (γ : ℝ) : Set (Returns n) :=
  {x | γ ≤ -inner ℝ x w}

/-- The quadratic form `wᵀΓw`. -/
def quadForm {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (w : Returns n) : ℝ :=
  ∑ i, ∑ j, w i * Γ i j * w j

/-- The reference Gaussian distribution `P₀ = 𝒩(x̂, Γ)` on `ℝⁿ`. -/
noncomputable def refGaussian {n : ℕ} (xhat : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Returns n) :=
  multivariateGaussian xhat Γ

/-- The relative-entropy class of Eq. (43): probability distributions `P` of returns with
`KL(P, P₀) ≤ d`, where `P₀ = 𝒩(x̂, Γ)`. Mathlib's `klDiv P P₀` is `∞` unless `P ≪ P₀` and the
log-likelihood ratio is `P`-integrable, and equals `∫ log (dP/dP₀) dP` otherwise (for
probability measures). -/
def klBall {n : ℕ} (xhat : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) :
    Set (Measure (Returns n)) :=
  {P | IsProbabilityMeasure P ∧ InformationTheory.klDiv P (refGaussian xhat Γ) ≤ ENNReal.ofReal d}

/-- The feasible set of the worst-case Value-at-Risk problem (4): the levels `γ` such that
`Prob{γ ≤ -r(w, x)} ≤ ε` for every distribution `P` in the class `Pclass` (the paper's `𝒫`), with `r(w, x) = wᵀx`.
The worst-case VaR `V_𝒫(w)` is the least element of this set, when it exists. -/
def varFeasible {n : ℕ} (Pclass : Set (Measure (Returns n))) (w : Returns n) (ε : ℝ) : Set ℝ :=
  {γ | ∀ P ∈ Pclass, P (lossSet w γ) ≤ ENNReal.ofReal ε}

/-- The cumulative distribution function `Φ` of the standard normal distribution. -/
noncomputable def stdNormalCDF (t : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) t

/-- The standard normal quantile: `Φ⁻¹(p) = inf {t | p ≤ Φ(t)}`. For `p ∈ (0, 1)` the set is
nonempty and bounded below, and this is the inverse of `Φ`; outside `(0, 1)` the value is not
meaningful (Lean's `sInf` returns `0` on an empty or unbounded-below set). -/
noncomputable def normalQuantile (p : ℝ) : ℝ :=
  sInf {t : ℝ | p ≤ stdNormalCDF t}

/-- The ratio `(e^{ε/λ - d} - 1) / (e^{1/λ} - 1)` whose supremum over `λ > 0` defines `f(ε, d)`
in Eq. (45). -/
noncomputable def entropyRatio (ε d lam : ℝ) : ℝ :=
  (Real.exp (ε / lam - d) - 1) / (Real.exp (1 / lam) - 1)

/-- `f(ε, d) := sup_{λ > 0} (e^{ε/λ - d} - 1) / (e^{1/λ} - 1)` of Eq. (45). For `ε ≤ 1` and
`d ≥ 0` the set of values is nonempty and bounded above by `1` (the numerator is smaller than
the positive denominator), so `sSup` is the true supremum there and not Lean's junk value. -/
noncomputable def fEntropy (ε d : ℝ) : ℝ :=
  sSup (entropyRatio ε d '' Set.Ioi 0)

/-- The entropy-constrained risk factor `κ(ε, d) := -Φ⁻¹(f(ε, d))` of Eq. (45). -/
noncomputable def kappaEntropy (ε d : ℝ) : ℝ :=
  -normalQuantile (fEntropy ε d)

/-- The Gaussian tail `φ(γ) := 1 - Φ((γ + wᵀx̂) / √(wᵀΓw))` (p. 554). -/
noncomputable def gaussianTail {n : ℕ} (xhat : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (w : Returns n) (γ : ℝ) : ℝ :=
  1 - stdNormalCDF ((γ + inner ℝ w xhat) / Real.sqrt (quadForm Γ w))

/-- The partially minimised dual function of Eq. (48):
`λ d + λ log((e^{1/λ} - 1) φ + 1)`. -/
noncomputable def dualValue (d φ lam : ℝ) : ℝ :=
  lam * d + lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1)

end WorstCaseVaR.Entropy
