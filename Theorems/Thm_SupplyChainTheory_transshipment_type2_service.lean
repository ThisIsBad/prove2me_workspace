import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem transshipment_type2_service (Sj Si : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di) (hpos : 0 < ∫ d, d ∂Di) :
    type2Trans Sj Si Dj Di
      = type2NoTrans Si Di + expTransship Sj Si Dj Di / (∫ d, d ∂Di) := by sorry

end SupplyChainTheory

