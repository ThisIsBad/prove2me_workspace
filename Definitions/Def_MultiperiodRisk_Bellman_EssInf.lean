import Mathlib

namespace MultiperiodRisk.Bellman

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `g` is an essential infimum of the family `S` of real functions, relative to the
sub-σ-algebra `m'` and the measure `μ`: the greatest `m'`-measurable function that is
`μ`-a.e. below every member of `S`. -/
def IsEssInf (μ : Measure Ω) (m' : MeasurableSpace Ω) (S : Set (Ω → ℝ)) (g : Ω → ℝ) : Prop :=
  StronglyMeasurable[m'] g ∧ (∀ h ∈ S, g ≤ᵐ[μ] h) ∧
    ∀ g' : Ω → ℝ, StronglyMeasurable[m'] g' → (∀ h ∈ S, g' ≤ᵐ[μ] h) → g' ≤ᵐ[μ] g

/-- A chosen essential infimum of the family `S` (unique up to `μ`-null sets). The fallback
value `0` is used only when no essential infimum exists. -/
noncomputable def essInfFamily (μ : Measure Ω) (m' : MeasurableSpace Ω) (S : Set (Ω → ℝ)) :
    Ω → ℝ := by
  classical
  exact if h : ∃ g, IsEssInf μ m' S g then h.choose else 0

end MultiperiodRisk.Bellman
