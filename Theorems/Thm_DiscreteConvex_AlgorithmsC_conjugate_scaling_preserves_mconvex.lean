import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_AlgorithmsC_ScaledConjugate
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScalingE
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScaling

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.41 (p.319). GOAL. For a dual-integral polyhedral M-convex function
`f = ConjugateFromZ g` (`g` L♮-convex), the conjugate scaling `f⟨α⟩` is again a dual-integral
polyhedral M-convex function, provided `f⟨α⟩ > -∞`. The conclusion is about `f⟨α⟩` itself: it
satisfies (M-EXC[R]) and lies in `M[R→R|Z]`, i.e. it is `ConjugateFromZ` of an L♮-convex function
(`g_α`). L♮-convexity of `g_α` alone is Theorem 7.10 (2) and a lemma of the proof, and leaves
`hprop` unused. -/
theorem conjugate_scaling_preserves_mconvex (g : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g)
    (alpha : ℤ) (halpha : 0 < alpha) (hprop : ∀ x, ConjugateScalingE g alpha x ≠ ⊥) :
    MExchangeAxiomR (ConjugateScaling g alpha) ∧
      LNaturalConvex (ScaledConjugate g alpha) ∧
      ConjugateScaling g alpha = ConjugateFromZ (ScaledConjugate g alpha) := by sorry

end DiscreteConvex.AlgorithmsC
