import Mathlib

namespace SAGA.StronglyConvex

/-- `IsProxPoint h γ y p`: the point `p` minimizes `x ↦ h x + 1/(2γ) ‖x - y‖²`, i.e.
`p` is a value of the proximal operator `prox_γ^h (y)` of Defazio–Bach–Lacoste-Julien (2014),
eq. (3), p. 2. -/
def IsProxPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → ℝ) (γ : ℝ) (y p : E) : Prop :=
  ∀ z : E, h p + 1 / (2 * γ) * ‖p - y‖ ^ 2 ≤ h z + 1 / (2 * γ) * ‖z - y‖ ^ 2

end SAGA.StronglyConvex
