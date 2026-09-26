import Mathlib

namespace KellyStochasticNetworks

theorem wardrop_objective_convex (D : ℝ → ℝ) (hD : Continuous D) (hmono : Monotone D) :
    ConvexOn ℝ Set.univ (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) := by sorry

end KellyStochasticNetworks
