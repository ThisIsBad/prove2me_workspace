import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- Equation (4), with the paper's index shifted down by one. -/
def stick (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (1 - y i)) * y k

/-- The (k+1)-st largest value, counted with multiplicity, for a nonnegative
sequence tending to zero. The extended cardinality also handles infinite
upper level sets without assigning them the finite cardinality zero. -/
noncomputable def ranked (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ {i | t < x i}.encard ≤ k}

/-- The independent beta stick factors of Definition 1. -/
def IsStickLaw (α θ : ℝ) (μ : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧
    iIndepFun (fun k (y : ℕ → ℝ) => y k) μ ∧
    ∀ k : ℕ, HasLaw (fun y : ℕ → ℝ => y k)
      (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) μ

/-- Definition 1: the distribution of the ranked stick lengths. -/
def HasPD {Ω : Type*} [MeasurableSpace Ω]
    (α θ : ℝ) (P : Measure Ω) (V : Ω → ℕ → ℝ) : Prop :=
  AEMeasurable V P ∧
    ∃ μ : Measure (ℕ → ℝ), IsStickLaw α θ μ ∧
      ∀ s : Set (ℕ → ℝ), MeasurableSet s →
        P (V ⁻¹' s) = μ ((fun y => ranked (stick y)) ⁻¹' s)

/-- Equation (21): ratio R_(k+1) of consecutive ranked masses. -/
noncomputable def ratio (v : ℕ → ℝ) (k : ℕ) : ℝ := v (k + 1) / v k

/-- Equation (23), reconstructing the ranked masses from the ratios. -/
noncomputable def fromRatios {Ω : Type*} (R : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) : ℝ :=
  let first := 1 / (1 + ∑' j : ℕ, ∏ i ∈ Finset.range (j + 1), R i ω)
  if k = 0 then first else
    first * ∏ i ∈ Finset.range k, R i ω

end PoissonDirichlet.Ratio
