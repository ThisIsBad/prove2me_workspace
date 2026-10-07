import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem fractional_cut_cuts_off_and_keeps_integer_optimum {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (m + 1))
    (h : ¬ IsInt (a i₀ 0)) :
    TableauSol a (fun i => a i 0) (fun _ => 0) ∧
    cutValue a i₀ (fun _ => 0) = -Int.fract (a i₀ 0) ∧
    ¬ FeasibleStar a i₀ (fun i => a i 0) (fun _ => 0)
      (cutValue a i₀ (fun _ => 0)) ∧
    (∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      NonnegIntSol a x t ↔ NonnegIntSolStar a i₀ x t (cutValue a i₀ t)) ∧
    (∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
      NonnegIntSolStar a i₀ x t s → s = cutValue a i₀ t) ∧
    (∀ W : ℝ,
      IsGreatest {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
        NonnegIntSol a x t ∧ x 0 = v} W ↔
      IsGreatest {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
        NonnegIntSolStar a i₀ x t s ∧ x 0 = v} W) := by sorry

end Gomory58.FractionalCut

