import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvexR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvexR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateArcR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsConvexUnivariateR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeROnT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeROnT

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.28 (p.271-272). The `R→R` analogue of Theorem 9.26 (real domain throughout, with
the conjugacy assertion restored, via the ordinary Legendre-Fenchel transform).  The induced functions are the book's functions **on `Zᵀ`** (resp. `Rᵀ`): read on
all of `Zⱽ` they are cylinders along `V ∖ T`, and the exchange axiom then fails whenever `T ≠ V`
(with `V = {s,t}`, `S = {s}`, `T = {t}`, one arc, `fa = 0` and `f` the indicator of `0`, `f̃(y) = 0`
iff `y(t) = 0`). -/
theorem network_transformation_rr (tail head : A → V) (S T : Finset V) (fa ga : A → ℝ → WithTop ℝ)
    (f g : (V → ℝ) → WithTop ℝ) (hfa : ∀ a, IsConvexUnivariateR (fa a))
    (hga : ∀ a, IsConvexUnivariateR (ga a))
    (hfbdd : ∀ y, InducedFTildeR tail head S T fa f y ≠ ⊥)
    (hfprop : ∃ y, InducedFTildeR tail head S T fa f y ≠ ⊤)
    (hgbdd : ∀ q, InducedGTildeR tail head S T ga g q ≠ ⊥)
    (hgprop : ∃ q, InducedGTildeR tail head S T ga g q ≠ ⊤) :
    (MExchangeAxiomR f → MExchangeAxiomR (InducedFTildeROnT tail head S T fa f)) ∧
    (MNaturalConvexR f → MNaturalConvexR (InducedFTildeROnT tail head S T fa f)) ∧
    ((SBFR g ∧ TRFR g) →
      SBFR (InducedGTildeROnT tail head S T ga g) ∧ TRFR (InducedGTildeROnT tail head S T ga g)) ∧
    (LNaturalConvexR g → LNaturalConvexR (InducedGTildeROnT tail head S T ga g)) ∧
    (MNaturalConvexR f → LNaturalConvexR g →
      g = ConvexConjugateR f → (∀ a, ga a = ConvexConjugateArcR (fa a)) →
      InducedGTildeROnT tail head S T ga g = ConvexConjugateR (InducedFTildeROnT tail head S T fa f)) := by sorry

end DiscreteConvex.NetworkFlowsC
