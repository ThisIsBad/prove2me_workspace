import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 100: under the coordinating options contract
(`r − w_e = λ(r − c_p)`, `w_o = λ c_k`, here with `λ ∈ (0, 1]`), the profit of a supplier who
believes demand is type `θ` and builds `k` after selling `q_i` options is
`π(k, q_i, θ) = (1 − λ)(r − c_p) S_θ(k) − c_k (k − λ q_i)`; at `q_i = k = k_θ°` its derivative in `k`
is negative, so `k_θ°` does not maximize the supplier's profit over `0 ≤ k ≤ q_i`. -/
theorem p100_voluntary_compliance (M : Model) (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) (hko_pos : 0 < ko) :
    (∀ k qi : ℝ, M.supVoluntaryProfit θ we wo k qi
        = (1 - lam) * (M.r - M.cp) * M.S θ k - M.ck * (k - lam * qi)) ∧
      (∃ d : ℝ, d < 0 ∧ HasDerivAt (fun k => M.supVoluntaryProfit θ we wo k ko) d ko) ∧
      ¬ IsMaxOn (fun k => M.supVoluntaryProfit θ we wo k ko) (Set.Icc 0 ko) ko := by sorry

end CachonCoord.CapacityForecast

