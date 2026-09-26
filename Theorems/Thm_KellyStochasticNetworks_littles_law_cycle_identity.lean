import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem littles_law_cycle_identity {N : ℕ} (T : ℝ) (a d : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (had : ∀ i, a i ≤ d i) (hd : ∀ i, d i ≤ T) :
    (∫ s in (0:ℝ)..T, occupancy a d s) = ∑ i, (d i - a i) := by sorry

end KellyStochasticNetworks