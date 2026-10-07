import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open MeasureTheory

/-- Continuation of equation (11) from `x > 0` to all real `x`, p. 799. -/
theorem equation_11_all (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : TailScaledConvergence μ a b (Set.Ioi 0)) :
    TailScaledConvergence μ a b Set.univ := by sorry

end BalkemaDeHaan.ExpDomain

