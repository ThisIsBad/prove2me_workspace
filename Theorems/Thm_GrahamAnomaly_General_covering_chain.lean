import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Display (1) in the proof of Theorem 1: a precedence chain ending at a
last-finishing task covers each time when a processor is idle. -/
theorem covering_chain {r n' : ℕ} (hr : 0 < r) (hn' : 0 < n')
    (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) [IsStrictOrder (Fin r) prec']
    (L' : Fin r ≃ Fin r) (G' : Schedule n' μ' prec')
    (hG' : IsListSchedule L' G') :
    ∃ c : List (Fin r), c.Chain' prec' ∧
      (∃ j ∈ c, G'.S j + μ' j = G'.finish) ∧
      ∀ t : ℝ, 0 ≤ t → t < G'.finish → ¬ AllBusy G' t →
        ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a := by sorry

end GrahamAnomaly.General

