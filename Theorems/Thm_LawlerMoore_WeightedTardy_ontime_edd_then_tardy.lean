import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy

namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared MooreLateJobs.NumLate

/-- §5 (p. 79): the on-time jobs of any sequence `l`, sequenced in order of their deadlines and
followed by the tardy jobs in arbitrary order, stay on time, and the weighted number of tardy
jobs does not increase (penalties `p j ≥ 0`). -/
theorem ontime_edd_then_tardy {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ E : List (Fin n),
      E.Nodup ∧
      (∀ j, j ∈ E ↔ j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) l) ∧
      E.Pairwise (fun i j => d i ≤ d j) ∧
      ∀ L : List (Fin n), IsSchedule Finset.univ (E ++ L) →
        (∀ j ∈ E, j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) (E ++ L)) ∧
        weightedTardy a' d p (E ++ L) ≤ weightedTardy a' d p l := by sorry

end LawlerMoore.WeightedTardy

