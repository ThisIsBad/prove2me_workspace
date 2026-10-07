import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 4, p. 19. If in addition to the hypotheses of Theorem 1 the functions `g` and
`h` are convex on `x ≥ 0`, then the solution `f` of Theorem 1 is convex on `x ≥ 0`, and for each
`x ≥ 0` the maximum in (8.1) is attained at `y = 0` or at `y = x`. -/
theorem convex_returns_endpoint_policy (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hh : ConvexOn ℝ (Set.Ici 0) h)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ConvexOn ℝ (Set.Ici 0) f ∧
      ∀ x : ℝ, 0 ≤ x → (allocT g h a b f x 0 = f x ∨ allocT g h a b f x x = f x) := by sorry

end BellmanDP.Allocation

