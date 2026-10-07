import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, pp. 74–75: the base-stock model is a newsvendor model.
With lead-time demand `D_r` as newsvendor demand and `c_r = g_r = g_s = v = 0`, the
newsvendor retailer's profit is `π_r(q) = pS(q) - wq = (p - w)q - pI(q)`, where
`S(q) = E[min(q, D_r)]` and `I(q) = E[(q - D_r)⁺]`. With `p = h_r + β_r` and `w = h_r`,
`π_r(q) = β_r q - (h_r + β_r)I_r(q) = -c_r(q) + β_r μ_r`, so maximizing `π_r` and
minimizing the base-stock cost `c_r` are the same problem. -/
theorem p75_newsvendor_equivalence (M : Model) :
    (∀ p w q : ℝ,
      p * SupplyChainTheory.expSales M.law q - w * q =
        (p - w) * q - p * SupplyChainTheory.expLeftover M.law q) ∧
    (∀ q : ℝ,
      (M.hr + M.br) * SupplyChainTheory.expSales M.law q - M.hr * q =
        M.br * q - (M.hr + M.br) * M.I q ∧
      M.br * q - (M.hr + M.br) * M.I q = -M.retailerCost q + M.br * M.meanDemand) ∧
    ∀ q : ℝ,
      IsMaxOn (fun x => (M.hr + M.br) * SupplyChainTheory.expSales M.law x - M.hr * x)
          Set.univ q ↔
        IsMinOn M.retailerCost Set.univ q := by sorry

end CachonCoord.BaseStock

