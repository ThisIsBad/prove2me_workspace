import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open MeasureTheory

/-- Equation (11) on `x > 0`, p. 799. -/
theorem equation_11_positive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : InDr μ piLaw) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧
      TailScaledConvergence μ a b (Set.Ioi 0) := by sorry

end BalkemaDeHaan.ExpDomain

