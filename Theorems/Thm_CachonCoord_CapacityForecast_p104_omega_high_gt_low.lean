import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.3, p. 104, implicit in "Since min{λ_h, λ̂_h} > λ_l" and in
"a lower profit (Ω_h(k_l°) vs. Ω_h°)": because `D_h` stochastically dominates `D_l`, the chain
earns more with high demand at every positive capacity, `Ω_l(k) < Ω_h(k)` for `k > 0`, and hence
the optimal high-type profit exceeds the optimal low-type profit, `Ω_l° < Ω_h°`, where `kh`, `kl`
are optimal capacities (maximizers of `Ω_h`, `Ω_l` over `k ≥ 0`) and `k_l° > 0`. -/
theorem p104_omega_high_gt_low (M : Model) (kh kl : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl) :
    (∀ k : ℝ, 0 < k → M.Omega DemandType.l k < M.Omega DemandType.h k) ∧
      M.Omega DemandType.l kl < M.Omega DemandType.h kh := by sorry

end CachonCoord.CapacityForecast

