import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.NonnegRank

/-- The operator `S : ℝⁿ × ℝⁿ → ℝ`, `S(x, y) = 1 − ⟨x, y⟩` (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §2, p. 3). The **slack operator** `S_C` of a convex body `C` is its restriction
to `ext(C) × ext(C°)`; every statement of this mission evaluates `slackOperator x y` only for
`x ∈ Set.extremePoints ℝ C` and `y ∈ Set.extremePoints ℝ (polar C)`. For a polytope with the origin
in its interior this is the canonical slack matrix (§3, p. 9). -/
noncomputable def slackOperator {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 - ⟪x, y⟫_ℝ

end ConeLifts.NonnegRank
