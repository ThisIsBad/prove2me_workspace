import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Bellman, *Dynamic Programming*, Ch. I, Theorem 1, p. 12. Under (1a)–(1c) the equation (8.1)
`f(x) = Max_{0 ≤ y ≤ x} [g(y) + h(x − y) + f(ay + b(x − y))]` has a solution on `x ≥ 0` that is
continuous at `x = 0` with value `0` there; it is continuous for all `x ≥ 0`; and every solution
continuous at `0` with value `0` there coincides with it on `x ≥ 0`. -/
theorem allocation_equation_exists_unique (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b) :
    ∃ f : ℝ → ℝ, IsAllocationSolution g h a b f ∧
      ContinuousWithinAt f (Set.Ici 0) 0 ∧ f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      ∀ F : ℝ → ℝ, IsAllocationSolution g h a b F →
        ContinuousWithinAt F (Set.Ici 0) 0 → F 0 = 0 →
        ∀ x : ℝ, 0 ≤ x → F x = f x := by sorry

end BellmanDP.Allocation

