import Mathlib
import Definitions.Def_CubicNewton_Shared_lamMin

namespace CubicNewton.Nonconvex

/-- The measure of local (second-order) optimality of Nesterov–Polyak 2006, Section 3, p. 184:
`μ_M(x) = max { √( (2/(L + M)) ‖f′(x)‖ ), −(2/(2L + M)) λₙ(f″(x)) }`,
with `g x` for `f′(x)`, `H x` for `f″(x)` and `lamMin` for the smallest eigenvalue `λₙ`. -/
noncomputable def muMeasure {n : ℕ} (L M : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (Real.sqrt (2 / (L + M) * ‖g x‖)) (-(2 / (2 * L + M)) * CubicNewton.Shared.lamMin (H x))

end CubicNewton.Nonconvex
