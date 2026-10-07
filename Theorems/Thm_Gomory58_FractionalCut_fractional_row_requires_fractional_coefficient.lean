import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem fractional_row_requires_fractional_coefficient {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (m + 1))
    (hconst : Int.fract (a i₀ 0) ≠ 0)
    (hcoeff : ∀ j : Fin n, Int.fract (a i₀ j.succ) = 0) :
    ¬ ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      TableauSol a x t ∧ IsInt (x i₀) ∧ (∀ j, IsInt (t j)) := by sorry

end Gomory58.FractionalCut

