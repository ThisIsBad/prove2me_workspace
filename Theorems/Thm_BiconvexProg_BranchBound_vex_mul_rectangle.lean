import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace BiconvexProg.BranchBound

/-- Theorem 2 (p. 275): on a rectangle `Ω = [l, L] × [m, M] ⊂ ℝ²`, the convex envelope of `xy` is
`max {mx + ly − lm, Mx + Ly − LM}`, at every point of `Ω`. -/
theorem vex_mul_rectangle (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc l L ×ˢ Set.Icc m M) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => q.1 * q.2) p =
      max (m * p.1 + l * p.2 - l * m) (M * p.1 + L * p.2 - L * M) := by sorry

end BiconvexProg.BranchBound
