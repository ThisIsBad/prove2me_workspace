import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem cut_value_integral {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : TableauSol a x t) (hx : IsInt (x i₀)) (ht : ∀ j, IsInt (t j)) :
    cutValue a i₀ t =
      ((Int.floor (a i₀ 0) : ℝ) +
        (∑ j : Fin n, (Int.floor (a i₀ j.succ) : ℝ) * (-t j)) - x i₀) ∧
    IsInt (cutValue a i₀ t) := by sorry

end Gomory58.FractionalCut

