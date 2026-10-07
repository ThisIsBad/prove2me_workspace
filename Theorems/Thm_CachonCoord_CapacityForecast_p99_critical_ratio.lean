import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 99, the critical-ratio display: `Ω_θ` is concave in
capacity, and a positive capacity `k` (footnote 46 assumes `k_θ° > 0`) is an optimal capacity,
i.e. maximizes `Ω_θ` over `k ≥ 0`, exactly when it satisfies the newsvendor critical ratio
`F̄_θ(k) = c_k / (r − c_p)`. -/
theorem p99_critical_ratio (M : Model) (θ : DemandType) :
    ConcaveOn ℝ (Set.Ici 0) (M.Omega θ) ∧
      ∀ k : ℝ, 0 < k →
        (IsMaxOn (M.Omega θ) (Set.Ici 0) k ↔ 1 - cdf (M.μ θ) k = M.ck / (M.r - M.cp)) := by sorry

end CachonCoord.CapacityForecast

