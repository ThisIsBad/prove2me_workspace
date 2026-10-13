import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsEmbedOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.58 (p.240). For an M-convex program, the dual objective and optimal-value
functions are themselves well behaved: L-(resp. L2-)concave and M-(resp. M2-)convex. As in
Theorem 8.57, the book's second case in (3) and (4) allows `+∞` and `-∞` to be mixed over `u`:
with `B` the line `{x₁ + x₂ = 0}` and `c(x) = x₁` on `B`, `φ₀` is `-∞` on `B` and `+∞` off it. -/
theorem lagrangian_dual_convexity (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hB : ExchangeAxiomB B) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r) :
    (IsNegOf (fun h => SBF h ∧ TRF h) (GRSmall c (fun _ => (0 : WithTop ℝ)) B) ∨
      ∀ y, GRSmall c (fun _ => (0 : WithTop ℝ)) B y = ⊥) ∧
    (IsNegOf L2Convex (GRSmall c r B) ∨ (∀ y, GRSmall c r B y = ⊥) ∨
      (∀ y, GRSmall c r B y = ⊤)) ∧
    (IsEmbedOf MExchangeAxiom (PhiR c (fun _ => (0 : WithTop ℝ)) B) ∨
      (∀ u, PhiR c (fun _ => (0 : WithTop ℝ)) B u = ⊤ ∨
        PhiR c (fun _ => (0 : WithTop ℝ)) B u = ⊥)) ∧
    (IsEmbedOf M2Convex (PhiR c r B) ∨ (∀ u, PhiR c r B u = ⊤ ∨ PhiR c r B u = ⊥)) := by sorry

end DiscreteConvex.ConjugacyDualityD

