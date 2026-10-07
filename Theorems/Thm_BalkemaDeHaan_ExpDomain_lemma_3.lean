import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- Lemma 3, p. 798: asymptotically negligible jumps of the BalkemaDeHaan.LimitTypes.tail. -/
theorem lemma_3 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hG : Continuous (cdf ν)) (h : InDr μ (cdf ν)) :
    Tendsto (fun x : ℝ => (μ (Set.Ici x)).toReal / BalkemaDeHaan.LimitTypes.tail μ x) atTop (nhds 1) := by sorry

end BalkemaDeHaan.ExpDomain

