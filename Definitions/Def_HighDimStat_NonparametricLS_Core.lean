import Mathlib

namespace HighDimStat.NonparametricLS

open MeasureTheory ProbabilityTheory

/-- The empirical (`L²(Pₙ)`) squared seminorm `‖g‖ₙ²` of a function `g : X → ℝ` relative to `n`
fixed design points `x : Fin n → X` — the quantity `‖f − f*‖ₙ²` appearing throughout Chapter 13
(e.g. the basic inequality (13.18), p. 423). -/
noncomputable def empiricalNormSq {X : Type*} {n : ℕ} (x : Fin n → X) (g : X → ℝ) : ℝ :=
  (∑ i, (g (x i)) ^ 2) / n

/-- The empirical (`L²(Pₙ)`) seminorm `‖g‖ₙ`. -/
noncomputable def empiricalNorm {X : Type*} {n : ℕ} (x : Fin n → X) (g : X → ℝ) : ℝ :=
  Real.sqrt (empiricalNormSq x g)

/-- A function class `H` is star-shaped (footnote 2, p. 422) if for every `h ∈ H` and every
`α ∈ [0, 1]`, the rescaled function `αh` also belongs to `H`. -/
def IsStarShaped {X : Type*} (H : Set (X → ℝ)) : Prop :=
  ∀ h ∈ H, ∀ α ∈ Set.Icc (0 : ℝ) 1, (fun z => α * h z) ∈ H

/-- The `f*`-shifted function class `F* := F − {f*}` (Eq. (13.15), p. 421). -/
def shiftedClass {X : Type*} (F : Set (X → ℝ)) (fStar : X → ℝ) : Set (X → ℝ) :=
  (fun f => fun z => f z - fStar z) '' F

/-- The (symmetric) difference class `∂F := F − F = {f₁ − f₂ | f₁, f₂ ∈ F}` (Eq. (13.22),
p. 424), used in Theorem 13.13 when `f*` is not assumed known. -/
def diffClass {X : Type*} (F : Set (X → ℝ)) : Set (X → ℝ) :=
  {g | ∃ f1 ∈ F, ∃ f2 ∈ F, g = fun z => f1 z - f2 z}

/-- `n` i.i.d. standard Gaussian variates `w : Fin n → Ω → ℝ` on a probability space `(Ω, P)`
— the noise variables `{wᵢ}` of the local Gaussian complexity (Eq. (13.16), p. 421). -/
def IsIIDStdGaussian {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (w : Fin n → Ω → ℝ) : Prop :=
  (∀ i, Measurable (w i)) ∧ iIndepFun w P ∧ ∀ i, Measure.map (w i) P = gaussianReal 0 1

/-- The local Gaussian complexity `Gₙ(δ; H)` of a function class `H` at radius `δ`
(Eq. (13.16), p. 421): the expectation, over the noise `w`, of the supremum over the
radius-`δ` slice `{h ∈ H | ‖h‖ₙ ≤ δ}` of the absolute empirical Gaussian process
`|(1/n) Σᵢ wᵢ h(xᵢ)|`. The supremum is taken over the subtype of this slice, which is always
nonempty when `0 ∈ H` (in particular whenever `H` is star-shaped and nonempty, since taking
`α = 0` on any `h ∈ H` shows `0 ∈ H`). -/
noncomputable def localGaussianComplexity {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) (H : Set (X → ℝ)) (δ : ℝ) : ℝ :=
  ∫ ω, ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ},
      |(∑ i, w i ω * h.1 (x i)) / n| ∂P

/-- `δ` satisfies the critical inequality (13.17)/(13.42a): `Gₙ(δ; H)/δ ≤ δ/(2σ)`, `δ > 0`.
A `δ` satisfying this is called *valid* in the book (p. 422). The explicit `Integrable`
hypothesis on the defining supremum (trap 2) guards against `localGaussianComplexity`'s
Bochner integral silently collapsing to Mathlib's junk value `0` on a non-measurable or
non-integrable integrand — a genuine risk since `X` and `H` carry no topology, separability or
countability constraint elsewhere in this file — which would otherwise make this predicate
(and every theorem that assumes it) trivially/vacuously satisfiable for every `δ > 0`. -/
def SatisfiesCriticalInequality {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) (H : Set (X → ℝ)) (σ δ : ℝ) : Prop :=
  0 < δ ∧
    MeasureTheory.Integrable
      (fun ω => ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ},
          |(∑ i, w i ω * h.1 (x i)) / n|) P ∧
    localGaussianComplexity x w P H δ / δ ≤ δ / (2 * σ)

/-- `fHat` is a nonparametric least-squares estimate over `F` for the observed data `y`
(Eq. (13.7)): `fHat ∈ F` and it minimizes the empirical sum of squared residuals over `F`. -/
def IsLeastSquaresEstimate {X : Type*} {n : ℕ} (x : Fin n → X) (F : Set (X → ℝ))
    (y : Fin n → ℝ) (fHat : X → ℝ) : Prop :=
  fHat ∈ F ∧ ∀ f ∈ F, ∑ i, (y i - fHat (x i)) ^ 2 ≤ ∑ i, (y i - f (x i)) ^ 2

end HighDimStat.NonparametricLS
