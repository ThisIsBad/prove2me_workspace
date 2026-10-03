import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_LiftedFunctionL
import Definitions.Def_DiscreteConvex_AlgorithmsC_Khat1
import Definitions.Def_DiscreteConvex_AlgorithmsC_K1
import Definitions.Def_DiscreteConvex_AlgorithmsC_KInfty

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.32 (p.307). For the lift `g̃` of an integer-domain function `g` to
`Option V` (Eq. (10.35)), `K̂₁(g̃) ≤ K₁(g) + n·K∞(g) ≤ min[(n+1)K₁(g), 2n·K∞(g)]`. -/
theorem khat1_lift_bound [Nonempty V] (g : (V → ℤ) → WithTop ℝ) :
    (Khat1 (LiftedFunctionL g) : ℝ) ≤ (K1 g : ℝ) + (Fintype.card V : ℝ) * (KInfty g : ℝ) ∧
    (K1 g : ℝ) + (Fintype.card V : ℝ) * (KInfty g : ℝ) ≤
      min ((Fintype.card V + 1 : ℝ) * (K1 g : ℝ)) (2 * (Fintype.card V : ℝ) * (KInfty g : ℝ)) := by sorry

end DiscreteConvex.AlgorithmsC
