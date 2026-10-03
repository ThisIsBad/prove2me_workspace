import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.44 (p.159-160). -/
theorem shared_convex_combination (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MNaturalConvex f1)
    (hf2 : MNaturalConvex f2) (x : V → ℝ) :
    ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ IntegralNeighborhoodFinset x, 0 ≤ lam y) ∧
      (∑ y ∈ IntegralNeighborhoodFinset x, lam y = 1) ∧
      (∀ v, ∑ y ∈ IntegralNeighborhoodFinset x, lam y * (y v : ℝ) = x v) ∧
      ConvexClosureVal f1 x =
        ((∑ y ∈ IntegralNeighborhoodFinset x, lam y * (f1 y).untopD 0 : ℝ) : WithTop ℝ) ∧
      ConvexClosureVal f2 x =
        ((∑ y ∈ IntegralNeighborhoodFinset x, lam y * (f2 y).untopD 0 : ℝ) : WithTop ℝ) := by sorry

end DiscreteConvex.MConvexFunctionsC
