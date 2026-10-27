import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_2 (P : Params) (hP : P.Standing) :
    ((∃ pN : ℝ, IsOptPriceN P pN) ∧
      ∃ uhat : ℝ, 0 < uhat ∧ ∀ ux : ℝ, 0 ≤ ux → ux ≤ uhat →
        (∃ p : ℝ, IsOptPrice P ux p) ∧
        ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN →
          profitN P pN < profit P ux p ∧ CSN P pN < CS P ux p) ∧
    (∃ ux : ℝ, 0 ≤ ux ∧ (∃ p : ℝ, IsOptPrice P ux p) ∧
      ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN →
        profit P ux p < profitN P pN) := by sorry

end ExpRetail.Monopoly

