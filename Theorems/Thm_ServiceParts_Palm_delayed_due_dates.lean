import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem delayed_due_dates {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.agedUnitsInResupply T t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF
        (S.rate * S.meanResupply *
          ((1 / S.meanResupply) * ∫ u in Set.Ioi T, (1 - S.resupplyCdf u)))
        S.sizePMF n)) := by sorry

end ServiceParts.Palm

