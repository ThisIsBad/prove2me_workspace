import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem adjacent_interchange (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (l₁ l₂ : List (Fin n)) (i j : Fin n)
    (hfeas : LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ i :: j :: l₂))
    (hon : ∀ x, MooreLateJobs.Shared.completionTime a (l₁ ++ i :: j :: l₂) x ≤ d x)
    (hlt : modifiedDeadline ρ d ε j < modifiedDeadline ρ d ε i) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ j :: i :: l₂) ∧
      ∀ x, MooreLateJobs.Shared.completionTime a (l₁ ++ j :: i :: l₂) x ≤ d x := by sorry

end LawlerMoore.PrecDeadline

