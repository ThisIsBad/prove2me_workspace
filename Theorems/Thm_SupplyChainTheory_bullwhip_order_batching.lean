import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_order_batching {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hN : 0 < N) (hR : 0 < R)
    (Br Bc Bb : BatchOrders P N R mu sigma)
    (hXr : ∀ j : ℕ, P.real {ω | Br.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j))
    (hXc0 : P.real {ω | Bc.X ω = 0} = 1 - 1 / R) (hXcN : P.real {ω | Bc.X ω = N} = 1 / R)
    (M k : ℕ) (hk : k < R) (hNMk : N = M * R + k)
    (hXbM : P.real {ω | Bb.X ω = M} = 1 - k / R)
    (hXbM1 : P.real {ω | Bb.X ω = M + 1} = k / R) :
    ((∫ ω, Bc.supplierOrder ω ∂P) = N * mu ∧ (∫ ω, Br.supplierOrder ω ∂P) = N * mu
        ∧ (∫ ω, Bb.supplierOrder ω ∂P) = N * mu)
      ∧ (ProbabilityTheory.variance Br.supplierOrder P
            ≤ ProbabilityTheory.variance Bc.supplierOrder P
          ∧ ProbabilityTheory.variance Bb.supplierOrder P
            ≤ ProbabilityTheory.variance Br.supplierOrder P
          ∧ N * sigma ^ 2 ≤ ProbabilityTheory.variance Bb.supplierOrder P) := by sorry

end SupplyChainTheory

