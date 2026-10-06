import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.33 (M2-optimality criterion; p.228). Global optimality of `f1+f2` is characterized
by a nonnegative-sum condition over disjoint cyclic exchanges. -/
theorem m2_optimality_criterion_summands (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MExchangeAxiom f1)
    (hf2 : MExchangeAxiom f2) (x : V → ℤ) (hx : x ∈ DomZ f1 ∩ DomZ f2) :
    (∀ y : V → ℤ, f1 x + f2 x ≤ f1 y + f2 y) ↔
      (∀ k : ℕ, ∀ u v : Fin (k + 1) → V, (∀ i j, u i ≠ v j) →
        (∑ i : Fin (k + 1),
            (f1 (fun w => x w - IndicatorVec {u i} w + IndicatorVec {v i} w) - f1 x)) +
          (∑ i : Fin (k + 1),
            (f2 (fun w => x w + IndicatorVec {u (i + 1)} w - IndicatorVec {v i} w) - f2 x)) ≥
          0) := by sorry

end DiscreteConvex.ConjugacyDualityC

