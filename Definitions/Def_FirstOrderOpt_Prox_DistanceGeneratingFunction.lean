import Mathlib

/-!
# Distance generating functions and Bregman distances (Lan, §3.2)

Lan, *First-order and Stochastic Optimization Methods for Machine Learning*, Springer 2020,
§3.2 (pp. 58–60): a *distance generating function* on a closed convex set `X` is a function
`ω : X → ℝ` that is continuously differentiable and strongly convex with modulus `1` with respect
to the norm `‖·‖`, i.e. (3.2.1)

  `ω(y) ≥ ω(x) + ⟨ω'(x), y - x⟩ + ½ ‖y - x‖²   for all x, y ∈ X`;

its *prox-function* (Bregman distance) is (3.2.2)

  `V(x, z) := ω(z) - ω(x) - ⟨ω'(x), z - x⟩`,

so that `V(x, z) ≥ ½ ‖z - x‖²` (3.2.3) and `V(x, x) = 0`. The same objects are used throughout
Chapters 3–8 (mirror descent, accelerated gradient, stochastic mirror descent, variance
reduction, nonconvex mirror descent, gradient sliding). This module packages them once so
that every theorem of the series states `V` as *this* object instead of a free function.

In a general normed space the gradient `ω'(x)` is a continuous linear functional
`E →L[ℝ] ℝ`, following the series' convention for gradients and subgradients.
-/

namespace FirstOrderOpt.Prox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A distance generating function on `X` (Lan §3.2): `ω` together with its gradient map `dω`,
differentiable along `X` with `dω` continuous on `X`, and `1`-strongly convex on `X` with respect
to `‖·‖` (3.2.1). -/
structure DistanceGeneratingFunction (X : Set E) where
  /-- The function `ω`. -/
  ω : E → ℝ
  /-- Its gradient `ω'(x)`, as a continuous linear functional. -/
  dω : E → E →L[ℝ] ℝ
  /-- `ω` is differentiable along `X` at every point of `X`, with derivative `dω x`. -/
  hasFDerivWithinAt : ∀ x ∈ X, HasFDerivWithinAt ω (dω x) X x
  /-- `ω` is continuously differentiable on `X`: the gradient map is continuous on `X`. -/
  continuousOn_dω : ContinuousOn dω X
  /-- Strong convexity with modulus `1` on `X` (3.2.1). -/
  strongConvex : ∀ x ∈ X, ∀ y ∈ X, ω x + dω x (y - x) + (1 / 2) * ‖y - x‖ ^ 2 ≤ ω y

/-- The prox-function / Bregman distance `V(x, z) = ω(z) - ω(x) - ⟨ω'(x), z - x⟩` (3.2.2). -/
noncomputable def DistanceGeneratingFunction.V {X : Set E} (ν : DistanceGeneratingFunction X)
    (x z : E) : ℝ :=
  ν.ω z - ν.ω x - ν.dω x (z - x)

end FirstOrderOpt.Prox
