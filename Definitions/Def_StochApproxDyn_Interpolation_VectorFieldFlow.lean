import Mathlib

namespace StochApproxDyn.Interpolation

/-- `y : ℝ → E` is an *integral curve* of the vector field `F` (a global solution of
`dy/dt = F(y)`): `y` is differentiable at every `t ∈ ℝ` with `y'(t) = F(y(t))`. -/
def IsIntegralCurveOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E)
    (y : ℝ → E) : Prop :=
  ∀ t : ℝ, HasDerivAt y (F (y t)) t

/-- `F` is *globally integrable* (Benaïm 1999, §4.1, p. 12): it has unique integral curves.
Through every point `p` there is an integral curve `y` defined on all of `ℝ` with `y(0) = p`, and
two integral curves with the same value at time `0` coincide. -/
def IsGloballyIntegrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E) :
    Prop :=
  (∀ p : E, ∃ y : ℝ → E, y 0 = p ∧ IsIntegralCurveOf F y) ∧
    ∀ y z : ℝ → E, IsIntegralCurveOf F y → IsIntegralCurveOf F z → y 0 = z 0 → y = z

/-- `Φ : ℝ → E → E` is the *flow induced by* `F`: for every `p`, `t ↦ Φ_t(p)` is the integral
curve of `F` through `p` at time `0`. If `F` is globally integrable, this determines `Φ`. -/
def IsFlowOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E)
    (Φ : ℝ → E → E) : Prop :=
  ∀ p : E, Φ 0 p = p ∧ IsIntegralCurveOf F (fun t => Φ t p)

end StochApproxDyn.Interpolation
