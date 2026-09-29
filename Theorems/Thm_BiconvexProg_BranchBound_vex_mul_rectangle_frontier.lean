import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace BiconvexProg.BranchBound

/-- Theorem 3 (p. 276): on a rectangle `Ω = [l, L] × [m, M] ⊂ ℝ²`, the convex envelope of `xy`
equals `xy` at every point of the boundary `∂Ω`. -/
theorem vex_mul_rectangle_frontier (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ frontier (Set.Icc l L ×ˢ Set.Icc m M)) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => q.1 * q.2) p = p.1 * p.2 := by sorry

end BiconvexProg.BranchBound
