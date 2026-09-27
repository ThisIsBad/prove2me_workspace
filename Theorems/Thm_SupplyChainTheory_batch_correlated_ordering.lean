import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem batch_correlated_ordering {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hR : 0 < R)
    (B : BatchOrders P N R mu sigma)
    (hX0 : P.real {ω | B.X ω = 0} = 1 - 1 / R) (hXN : P.real {ω | B.X ω = N} = 1 / R) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ ProbabilityTheory.variance B.supplierOrder P
          = N * sigma ^ 2 + mu ^ 2 * (N : ℝ) ^ 2 * (R - 1) := by sorry

end SupplyChainTheory

