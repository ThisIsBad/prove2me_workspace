import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
open Filter Topology
theorem corollary2_cesaro_vanish (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U)
    (l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U) (hlu : l ≤ u - M.b)
    (σ : ℕ → ℕ → ℤ → ℤ) (hσ : ∀ t s, s ≤ t → FeasibleL M U (yInf - M.b) (σ t s)) :
    ∀ x ≤ U, Tendsto (fun t : ℕ =>
        Pcomp M (σ t) t (H M U l u (fun _ => (1 : ℝ≥0∞)) + H M U l u (fun y => ENNReal.ofReal (M.G y))) x /
          ((t : ℝ≥0∞) + 1)) atTop (𝓝 0) := by sorry
end FedergruenZipkin.AvgCost

