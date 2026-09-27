import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem transshipment_type1_service (Sj Si : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    [MeasureTheory.NullSingletonClass Dj] [MeasureTheory.NullSingletonClass Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di) :
    ∃ dY : ℝ, HasDerivAt (fun s => expTransship Sj s Dj Di) dY Si ∧ dY ≤ 0
      ∧ type1Trans Sj Si Dj Di = type1NoTrans Si Di + |dY| := by sorry

end SupplyChainTheory

