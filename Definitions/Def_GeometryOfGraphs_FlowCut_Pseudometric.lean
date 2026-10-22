import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- A (semi-)metric on a set `X`, given as a distance function: `d x x = 0`, `d ≥ 0`, symmetry and the
triangle inequality. Two distinct points may be at distance zero (Linial–London–Rabinovich,
Combinatorica 15 (1995), p. 218, footnote 1: "we are discussing semi-metrics"). -/
def IsPseudometric {X : Type*} (d : X → X → ℝ) : Prop :=
  (∀ x, d x x = 0) ∧ (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = d y x) ∧
    (∀ x y z, d x z ≤ d x y + d y z)

end GeometryOfGraphs.FlowCut
