import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem batch_random_ordering {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hR : 0 < R)
    (B : BatchOrders P N R mu sigma)
    (hX : ∀ j : ℕ, P.real {ω | B.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j)) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ ProbabilityTheory.variance B.supplierOrder P
          = N * sigma ^ 2 + mu ^ 2 * N * (R - 1) := by sorry

end SupplyChainTheory

