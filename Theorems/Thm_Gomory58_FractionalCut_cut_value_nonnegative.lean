import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem cut_value_nonnegative {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : NonnegIntSol a x t) :
    -Int.fract (a i₀ 0) ≤ cutValue a i₀ t ∧ 0 ≤ cutValue a i₀ t := by sorry

end Gomory58.FractionalCut

