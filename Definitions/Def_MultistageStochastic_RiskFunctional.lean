import Mathlib

open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The random variables the risk functionals of Chapter 3 act on: `L^∞`, the measurable and
essentially bounded functions.  Pflug and Pichler, *Multistage Stochastic Optimization*, §3.1,
p. 96. -/
def MemLinfty (P : Measure Ω) (Y : Ω → ℝ) : Prop :=
  Measurable Y ∧ ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C

/-- Definition 3.2, the axioms for a **positively homogeneous risk functional** — what the book
calls a risk functional unless it says otherwise, and what is elsewhere called a coherent risk
measure: monotonicity (M), convexity (C), translation equivariance (T) and positive homogeneity
(H).  Pflug and Pichler, §3.1, p. 96. -/
structure IsRiskFunctional (P : Measure Ω) (R : (Ω → ℝ) → ℝ) : Prop where
  /-- (M) `R Y₁ ≤ R Y₂` whenever `Y₁ ≤ Y₂` almost surely. -/
  mono : ∀ Y₁ Y₂, MemLinfty P Y₁ → MemLinfty P Y₂ → (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) → R Y₁ ≤ R Y₂
  /-- (C) `R` is convex along linear interpolation. -/
  convex : ∀ Y₀ Y₁ (t : ℝ), MemLinfty P Y₀ → MemLinfty P Y₁ → 0 ≤ t → t ≤ 1 →
    R (fun ω => (1 - t) * Y₀ ω + t * Y₁ ω) ≤ (1 - t) * R Y₀ + t * R Y₁
  /-- (T) adding a constant to the loss adds it to the risk. -/
  translation : ∀ Y (c : ℝ), MemLinfty P Y → R (fun ω => Y ω + c) = R Y + c
  /-- (H) `R` is positively homogeneous. -/
  homogeneous : ∀ Y (t : ℝ), MemLinfty P Y → 0 < t → R (fun ω => t * Y ω) = t * R Y

/-- Definition 3.12: a functional is **version independent** (law invariant) when its value
depends on the distribution of its argument only.  Pflug and Pichler, §3.3, p. 103. -/
def VersionIndependent (P : Measure Ω) (R : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Y Y', MemLinfty P Y → MemLinfty P Y' →
    (∀ y : ℝ, P {ω | Y ω ≤ y} = P {ω | Y' ω ≤ y}) → R Y = R Y'

/-- The **Value-at-Risk** at level `α`, formula (3.2): `inf {y : P(Y ≤ y) ≥ α}`, the lower
inverse of the distribution function.  Pflug and Pichler, §3.2, p. 97. -/
noncomputable def valueAtRisk (P : Measure Ω) (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  sInf {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}}

/-- The essential supremum in the form the source uses, `ess sup Y = sup {y : G_Y(y) < 1}`.
Pflug and Pichler, §3.2, p. 97. -/
noncomputable def essSupBook (P : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  sSup {y : ℝ | P {ω | Y ω ≤ y} < 1}

/-- The (upper) **Average Value-at-Risk** at level `α`, Definition 3.3 (3.1):
`AV@R_α(Y) = (1-α)⁻¹ ∫_α^1 V@R_p(Y) dp` for `α ∈ [0,1)`, extended to `α = 1` by the limit, which
the source identifies with the essential supremum.  Pflug and Pichler, §3.2, p. 97. -/
noncomputable def averageValueAtRisk (P : Measure Ω) (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  if α = 1 then essSupBook P Y
  else (1 - α)⁻¹ * ∫ p in Set.Ioo α 1, valueAtRisk P Y p

/-- A probability space is **without atoms** when every set of positive measure splits into two
sets of smaller, positive measure.  The hypothesis of Kusuoka's theorem, Pflug and Pichler,
§3.3.1, p. 103. -/
def Atomless (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < P s →
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ 0 < P t ∧ P t < P s

/-- The measures appearing in a Kusuoka representation: probability measures carried by the unit
interval.  Pflug and Pichler, §3.3.1, p. 103. -/
def IsKusuokaMeasure (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0

end MultistageStochastic
