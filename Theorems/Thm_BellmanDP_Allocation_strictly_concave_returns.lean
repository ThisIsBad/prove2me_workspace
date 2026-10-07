import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 5, p. 20. If in addition to the hypotheses of Theorem 1 the functions `g` and
`h` are strictly concave on `x ≥ 0`, then the solution `f` of Theorem 1 is strictly concave on
`x ≥ 0`, and for each `x ≥ 0` the maximizing `y ∈ [0, x]` in (8.1) is unique. -/
theorem strictly_concave_returns (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (hg : StrictConcaveOn ℝ (Set.Ici 0) g) (hh : StrictConcaveOn ℝ (Set.Ici 0) h)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    StrictConcaveOn ℝ (Set.Ici 0) f ∧
      ∀ x : ℝ, 0 ≤ x → ∃! y : ℝ, y ∈ Set.Icc 0 x ∧ allocT g h a b f x y = f x := by sorry

end BellmanDP.Allocation

