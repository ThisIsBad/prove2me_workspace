import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model
import Definitions.Def_BellmanDP_Allocation_PolicyReturn

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 3, p. 18. Let `y₀` be continuous on `x ≥ 0` with `0 ≤ y₀(x) ≤ x`, and let
`f₀` be the return of the stationary policy `y₀` (the solution (11.10) of `f₀(x) = T(f₀, y₀(x))`).
Under the hypotheses of Theorem 1 the successive approximations
`f_{N+1}(x) = Max_{0 ≤ y ≤ x} T(f_N, y)` are monotone nondecreasing in `N` on `x ≥ 0` and converge
to the solution `f` of Theorem 1 uniformly on every finite interval `[0, R]`. -/
theorem policy_space_approximation_monotone (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (y₀ : ℝ → ℝ) (hy₀ : ContinuousOn y₀ (Set.Ici 0))
    (hy₀r : ∀ x : ℝ, 0 ≤ x → 0 ≤ y₀ x ∧ y₀ x ≤ x)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    (∀ N : ℕ, ∀ x : ℝ, 0 ≤ x →
        allocIter g h a b (policyReturn g h a b y₀) N x ≤
          allocIter g h a b (policyReturn g h a b y₀) (N + 1) x) ∧
      ∀ R : ℝ, 0 ≤ R →
        TendstoUniformlyOn (allocIter g h a b (policyReturn g h a b y₀)) f Filter.atTop
          (Set.Icc 0 R) := by sorry

end BellmanDP.Allocation

