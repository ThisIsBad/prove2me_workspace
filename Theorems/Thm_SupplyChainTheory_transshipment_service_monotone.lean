import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem transshipment_service_monotone (Sj : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di)
    (hposi : 0 < ∫ d, d ∂Di) (hposj : 0 < ∫ d, d ∂Dj) :
    Monotone (fun Si => type1Trans Sj Si Dj Di) ∧ Monotone (fun Si => type2Trans Sj Si Dj Di)
      ∧ Monotone (fun Si => type1Trans Si Sj Di Dj)
      ∧ Monotone (fun Si => type2Trans Si Sj Di Dj) := by sorry

end SupplyChainTheory

