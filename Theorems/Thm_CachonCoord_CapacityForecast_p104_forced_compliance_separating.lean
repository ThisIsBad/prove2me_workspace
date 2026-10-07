import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.3, pp. 103–104, the forced-compliance separating contracts.
`kh`, `kl` are optimal capacities `k_h°, k_l° > 0` (maximizers of `Ω_h`, `Ω_l` over `k ≥ 0`),
`piHat` is the supplier's minimum acceptable profit `π̂` with `0 < π̂ < Ω_l°`, and `Ω_l(k_h°) > 0`.
The low type offers the coordinating options contract with share `λ_l = 1 − π̂/Ω_l°` and initial
order `k_l°`; the high type offers share `λ_H = min{λ_h, λ̂_h}`, `λ_h = 1 − π̂/Ω_h°`,
`λ̂_h = (Ω_l° − π̂)/Ω_l(k_h°)`, and initial order `k_h°`; under forced compliance `k = q_i`. Then:
both shares lie in `(0, 1)` and `λ_l < λ_h`, `λ_l < λ̂_h`; the high type strictly prefers her contract
to the low type's; the low type weakly prefers hers to the high type's; the supplier earns exactly
`π̂` from the low type, at least `π̂` from the high type, and exactly `π̂` when `λ_h ≤ λ̂_h`; and each
type's initial order maximizes both her own and the supplier's profit (coordination). -/
theorem p104_forced_compliance_separating (M : Model) (kh kl piHat : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh) (hkh_pos : 0 < kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl)
    (hpi_pos : 0 < piHat) (hpi_lt : piHat < M.Omega DemandType.l kl)
    (hcross : 0 < M.Omega DemandType.l kh) :
    let lamL := M.shareLow kl piHat
    let lamH := min (M.shareHigh kh piHat) (M.shareHighHat kh kl piHat)
    -- the shares are admissible and the high type's share is larger
    (0 < lamL ∧ lamL < 1 ∧ 0 < lamH ∧ lamH < 1) ∧
    (lamL < M.shareHigh kh piHat ∧ lamL < M.shareHighHat kh kl piHat ∧ lamL < lamH) ∧
    -- the high type does not mimic the low type
    M.mfrProfit DemandType.h (M.optWe lamL) (M.optWo lamL) kl
      < M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    -- the low type does not mimic the high type
    M.mfrProfit DemandType.l (M.optWe lamH) (M.optWo lamH) kh
      ≤ M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl ∧
    -- the supplier's participation
    M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl = piHat ∧
    piHat ≤ M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    (M.shareHigh kh piHat ≤ M.shareHighHat kh kl piHat →
      M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh = piHat) ∧
    -- coordination: each type's initial order is optimal for her and for the supplier
    IsMaxOn (fun q => M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh ∧
    IsMaxOn (fun q => M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh := by sorry

end CachonCoord.CapacityForecast

