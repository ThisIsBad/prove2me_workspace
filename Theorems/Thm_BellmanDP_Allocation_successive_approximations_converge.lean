import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 2, p. 16. Under the hypotheses of Theorem 1, the successive approximations
`f_{N+1}(x) = Max_{0 ≤ y ≤ x} T(f_N, y)` started from any `f₀` continuous on `x ≥ 0` with
`f₀(0) = 0` converge to the solution `f` of Theorem 1 uniformly on every finite interval
`[0, R]`. -/
theorem successive_approximations_converge (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (f₀ : ℝ → ℝ) (hf₀ : ContinuousOn f₀ (Set.Ici 0)) (hf₀0 : f₀ 0 = 0)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ∀ R : ℝ, 0 ≤ R →
      TendstoUniformlyOn (allocIter g h a b f₀) f Filter.atTop (Set.Icc 0 R) := by sorry

end BellmanDP.Allocation

