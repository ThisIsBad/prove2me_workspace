import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.Shared

/-- The smallest eigenvalue `λₙ(A)` of a (self-adjoint) operator on `ℝⁿ`, written as the
Rayleigh-quotient infimum `inf_{‖v‖ = 1} ⟨A v, v⟩` (Nesterov–Polyak 2006, p. 180, Notation:
eigenvalues are numbered decreasingly, so `λₙ` is the smallest). For `n ≥ 1` the unit sphere is
nonempty and the quadratic form is bounded below by `−‖A‖`, so this is a genuine infimum; for
`n = 0` the sphere is empty and Lean's real `⨅` returns `0`. -/
noncomputable def lamMin {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨅ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪A v, v⟫

end CubicNewton.Shared
