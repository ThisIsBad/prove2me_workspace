import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem sorted_isFeasible (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ l := by sorry

end LawlerMoore.PrecDeadline

