import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

/-- Corollary, first clause (p. 276): on a box `Ω ⊂ ℝⁿ × ℝⁿ`, the convex envelope of `xᵀy` is the
sum of the convex envelopes of `x_i y_i` over the coordinate rectangles `Ω_i`. -/
theorem vex_bilinear_separable {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hz : z ∈ Ω.toSet) :
    convexEnvelope Ω.toSet bilin z =
      ∑ i, convexEnvelope (Ω.rect i) (fun p : ℝ × ℝ => p.1 * p.2) (z.1 i, z.2 i) := by sorry

end BiconvexProg.BranchBound
