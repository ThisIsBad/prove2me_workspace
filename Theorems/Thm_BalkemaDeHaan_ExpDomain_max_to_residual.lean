import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open MeasureTheory

/-- The `D(Λ) ∩ D₀ ⊆ D_r(Π)` half of Theorem 3, pp. 798–799. -/
theorem max_to_residual (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmax : InD μ lambdaLaw) (hpositive : InDZero μ) :
    InDr μ piLaw := by sorry

end BalkemaDeHaan.ExpDomain

