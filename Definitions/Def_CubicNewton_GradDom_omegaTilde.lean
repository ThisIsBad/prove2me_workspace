import Mathlib

namespace CubicNewton.GradDom

/-- The threshold `ω̃ = L₀⁴ / (324 (L + L₀)⁶ τ_f³)` of Nesterov–Polyak 2006, Theorem 7, (4.14),
p. 194, where `L` is the Lipschitz constant of the Hessian, `L₀ ∈ (0, L]` the lower bound on the
regularization parameters of method (3.3) and `τ_f` the constant of gradient domination (4.7). -/
noncomputable def omegaTilde (L₀ L τ : ℝ) : ℝ :=
  L₀ ^ 4 / (324 * (L + L₀) ^ 6 * τ ^ 3)

end CubicNewton.GradDom
