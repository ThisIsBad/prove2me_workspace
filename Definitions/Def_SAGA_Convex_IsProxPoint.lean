import Mathlib

namespace SAGA.Convex

/-- `p` is a minimizer of `h(z) + (1/(2γ)) ‖z - y‖²` over `z`, i.e. `p = prox_γ^h(y)`
(Defazio–Bach–Lacoste-Julien, p. 2, eq. (3)). -/
def IsProxPoint {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ) (γ : ℝ)
    (y p : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin d),
    h p + 1 / (2 * γ) * ‖p - y‖ ^ 2 ≤ h z + 1 / (2 * γ) * ‖z - y‖ ^ 2

end SAGA.Convex
