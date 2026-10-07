import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open MeasureTheory

/-- Theorem 3, p. 798: the exponential residual-life domain. -/
theorem theorem_3 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    InDr μ piLaw ↔ InD μ lambdaLaw ∧ InDZero μ := by sorry

end BalkemaDeHaan.ExpDomain

