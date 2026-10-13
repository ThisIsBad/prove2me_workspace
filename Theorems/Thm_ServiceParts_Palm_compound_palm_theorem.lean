import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem compound_palm_theorem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.unitsInResupply t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF (S.rate * S.meanResupply) S.sizePMF n)) := by sorry

end ServiceParts.Palm

