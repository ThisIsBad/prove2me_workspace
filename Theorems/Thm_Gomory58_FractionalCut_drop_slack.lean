import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem drop_slack {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) :
    (FeasibleStar a i₀ x t s → FeasibleSol a x t) ∧
    (NonnegIntSolStar a i₀ x t s → NonnegIntSol a x t) := by sorry

end Gomory58.FractionalCut

