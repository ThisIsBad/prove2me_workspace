import Mathlib

noncomputable section

namespace AccelScal.UCRace

/-- The joint law of two independent exponential discovery times. -/
def exponentialRace (rate1 rate2 : ℝ) : MeasureTheory.Measure (ℝ × ℝ) :=
  (ProbabilityTheory.expMeasure rate1).prod (ProbabilityTheory.expMeasure rate2)

end AccelScal.UCRace
