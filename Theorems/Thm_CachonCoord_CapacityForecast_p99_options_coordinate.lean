import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, pp. 99–100: with `k = q_i`, an options contract whose
parameters satisfy `r − w_e = λ(r − c_p)` and `w_o = λ c_k` with `λ ∈ [0, 1]` gives the manufacturer
`Π_θ(q_i) = λ Ω_θ(q_i)` and the supplier `(1 − λ) Ω_θ(q_i)`; hence an optimal capacity `k_θ°`
(a maximizer of `Ω_θ` over `k ≥ 0`) is an optimal order for the manufacturer and also maximizes
the supplier's profit. -/
theorem p99_options_coordinate (M : Model) (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) :
    (∀ qi : ℝ, M.mfrProfit θ we wo qi = lam * M.Omega θ qi) ∧
      (∀ qi : ℝ, M.supProfit θ we wo qi = (1 - lam) * M.Omega θ qi) ∧
      IsMaxOn (fun qi => M.mfrProfit θ we wo qi) (Set.Ici 0) ko ∧
      IsMaxOn (fun qi => M.supProfit θ we wo qi) (Set.Ici 0) ko := by sorry

end CachonCoord.CapacityForecast

