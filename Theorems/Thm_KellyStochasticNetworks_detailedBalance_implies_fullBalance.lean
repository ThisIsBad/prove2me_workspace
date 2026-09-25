import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem detailedBalance_implies_fullBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (h : DetailedBalance π q) : FullBalance π q := by sorry

end KellyStochasticNetworks
