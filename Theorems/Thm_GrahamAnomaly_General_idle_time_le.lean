import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Display (2), using the empty-task-time identity in (5). -/
theorem idle_time_le {r n' : ℕ} (hn' : 0 < n')
    (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) [IsStrictOrder (Fin r) prec']
    (G' : Schedule n' μ' prec') (c : List (Fin r))
    (hc : c.Chain' prec')
    (hcover : ∀ t : ℝ, 0 ≤ t → t < G'.finish → ¬ AllBusy G' t →
      ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a) :
    (n' : ℝ) * G'.finish - ∑ j, μ' j ≤
      ((n' : ℝ) - 1) * (c.map μ').sum := by sorry

end GrahamAnomaly.General

