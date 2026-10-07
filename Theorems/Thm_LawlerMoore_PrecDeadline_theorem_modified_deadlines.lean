import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem theorem_modified_deadlines (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (hrefl : ∀ j, ρ j j)
    (hantisymm : ∀ i j, ρ i j → ρ j i → i = j)
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    (∃ l' : List (Fin n), LawlerPrec.MinMax.IsFeasible ρ Finset.univ l' ∧
        ∀ j, MooreLateJobs.Shared.completionTime a l' j ≤ d j) ↔
      ∀ j, MooreLateJobs.Shared.completionTime a l j ≤ d j := by sorry

end LawlerMoore.PrecDeadline

