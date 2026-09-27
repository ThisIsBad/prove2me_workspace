import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem batch_balanced_ordering {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hR : 0 < R)
    (B : BatchOrders P N R mu sigma) (M k : ℕ) (hk : k < R) (hN : N = M * R + k)
    (hXM : P.real {ω | B.X ω = M} = 1 - k / R)
    (hXM1 : P.real {ω | B.X ω = M + 1} = k / R) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ ProbabilityTheory.variance B.supplierOrder P
          = N * sigma ^ 2 + mu ^ 2 * k * (R - k) := by sorry

end SupplyChainTheory

