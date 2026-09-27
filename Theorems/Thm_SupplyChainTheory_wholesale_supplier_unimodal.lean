import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_supplier_unimodal (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (f : ℝ → ℝ)
    (hdens : D = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (hIGFR : IGFR f D)
    (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0) :
    ∃ Qs, 0 < Qs ∧ StrictMonoOn (supplierInducedProfit P D) (Set.Icc 0 Qs)
      ∧ StrictAntiOn (supplierInducedProfit P D) (Set.Ici Qs) := by sorry

end SupplyChainTheory

