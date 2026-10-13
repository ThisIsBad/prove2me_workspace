import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupermodularPair

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.2 (p.207). For a supermodular function `f` in two variables, `f•` is
submodular. -/
theorem supermodular_pair_conjugate_submodular (f : (Fin 2 → ℝ) → WithTop ℝ)
    (hf : SupermodularPair f) :
    ∀ p q : Fin 2 → ℝ, ConvexConjugateRW f p + ConvexConjugateRW f q ≥
      ConvexConjugateRW f (p ⊔ q) + ConvexConjugateRW f (p ⊓ q) := by sorry

end DiscreteConvex.ConjugacyDualityB

