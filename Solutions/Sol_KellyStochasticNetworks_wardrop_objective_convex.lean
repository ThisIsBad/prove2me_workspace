import Mathlib

namespace KellyStochasticNetworks

end KellyStochasticNetworks

open KellyStochasticNetworks
theorem solution (D : ℝ → ℝ) (hD : Continuous D) (hmono : Monotone D) :
    ConvexOn ℝ Set.univ (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) := by
  have hderiv : deriv (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) = D := by
    funext y
    exact Continuous.deriv_integral D hD 0 y
  have hdiff : Differentiable ℝ (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) :=
    fun y => (hD.integral_hasStrictDerivAt 0 y).hasDerivAt.differentiableAt
  exact Monotone.convexOn_univ_of_deriv hdiff (by rw [hderiv]; exact hmono)

