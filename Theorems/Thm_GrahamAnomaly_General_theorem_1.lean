import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Graham's Theorem 1: shortening tasks, relaxing precedence, changing the
priority list, and changing the processor count have this bounded effect. -/
theorem theorem_1 {r n n' : ℕ} (hr : 0 < r) (hn : 0 < n) (hn' : 0 < n')
    (μ μ' : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (hμ' : ∀ j, 0 < μ' j) (hle : ∀ j, μ' j ≤ μ j)
    (prec prec' : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) prec] [IsStrictOrder (Fin r) prec']
    (hsub : ∀ i j, prec' i j → prec i j)
    (L L' : Fin r ≃ Fin r)
    (G : Schedule n μ prec) (G' : Schedule n' μ' prec')
    (hG : IsListSchedule L G) (hG' : IsListSchedule L' G') :
    G'.finish / G.finish ≤ 1 + ((n : ℝ) - 1) / n' := by sorry

end GrahamAnomaly.General

