import Mathlib

namespace TalagrandConc.SKModel

/-- The unordered interaction edges, represented by pairs with the smaller index first. -/
abbrev Interaction (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

/-- A spin takes the values `-1` and `1`; `Bool.true` denotes `1`. -/
def spin {N : ℕ} (ε : Fin N → Bool) (i : Fin N) : ℝ :=
  if ε i then 1 else -1

/-- The Gibbs partition function of (12.1), normalized by the number of spin configurations. -/
noncomputable def partitionFunction (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) : ℝ :=
  ((2 : ℝ) ^ N)⁻¹ *
    ∑ ε : Fin N → Bool,
      Real.exp ((β / Real.sqrt N) *
        ∑ p : Interaction N, h p * spin ε p.1.1 * spin ε p.1.2)

/-- The log partition function. -/
noncomputable def freeEnergy (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) : ℝ :=
  Real.log (partitionFunction N β h)

/-- The common product law of the independent interactions. -/
noncomputable def couplingLaw (N : ℕ) (ν : MeasureTheory.Measure ℝ) :
    MeasureTheory.Measure (Interaction N → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Interaction N => ν)

/-- The standing centered, normalized, zero-third-moment, locally exponential-integrable law. -/
def AdmissibleLaw (ν : MeasureTheory.Measure ℝ) : Prop :=
  MeasureTheory.Integrable (fun x : ℝ => x) ν ∧
  MeasureTheory.Integrable (fun x : ℝ => x ^ 2) ν ∧
  MeasureTheory.Integrable (fun x : ℝ => x ^ 3) ν ∧
  (∫ x : ℝ, x ∂ν) = 0 ∧
  (∫ x : ℝ, x ^ 2 ∂ν) = 1 ∧
  (∫ x : ℝ, x ^ 3 ∂ν) = 0 ∧
  ∃ α : ℝ, 0 < α ∧ MeasureTheory.Integrable (fun x : ℝ => Real.exp (α * |x|)) ν

/-- The extra two-sided exponential moment condition of Theorem 12.1. -/
def LightTails (ν : MeasureTheory.Measure ℝ) : Prop :=
  MeasureTheory.Integrable (fun x : ℝ => Real.exp x) ν ∧
  MeasureTheory.Integrable (fun x : ℝ => Real.exp (-x)) ν ∧
  (∫ x : ℝ, Real.exp x ∂ν) < 2 ∧
  (∫ x : ℝ, Real.exp (-x) ∂ν) < 2

/-- A median, in the paper's two-sided probability sense. -/
def IsMedian (N : ℕ) (ν : MeasureTheory.Measure ℝ) (β M : ℝ) : Prop :=
  (couplingLaw N ν {h | freeEnergy N β h ≤ M}).toReal ≥ 1 / 2 ∧
  (couplingLaw N ν {h | M ≤ freeEnergy N β h}).toReal ≥ 1 / 2

end TalagrandConc.SKModel
