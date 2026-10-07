import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Displays (3)–(4): the same chain in the relaxed order is a chain in the
original order, and its processing time cannot exceed the original finish. -/
theorem chain_sum_le_finish {r n : ℕ}
    (μ μ' : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (hle : ∀ j, μ' j ≤ μ j)
    (prec prec' : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) prec] [IsStrictOrder (Fin r) prec']
    (hsub : ∀ i j, prec' i j → prec i j)
    (G : Schedule n μ prec) (c : List (Fin r)) (hc : c.Chain' prec') :
    (c.map μ').sum ≤ (c.map μ).sum ∧ (c.map μ).sum ≤ G.finish := by sorry

end GrahamAnomaly.General

