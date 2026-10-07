import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- Gnedenko's criterion, used in the proof of Theorem 3, p. 798. -/
theorem gnedenko_criterion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) lambdaLaw ↔
      TailScaledConvergence μ a b Set.univ := by sorry

end BalkemaDeHaan.ExpDomain

