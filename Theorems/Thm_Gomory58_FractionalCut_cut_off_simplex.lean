import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem cut_off_simplex {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (h : ¬ IsInt (a i₀ 0)) :
    cutValue a i₀ (fun _ => 0) = -Int.fract (a i₀ 0) ∧
    cutValue a i₀ (fun _ => 0) < 0 := by sorry

end Gomory58.FractionalCut

