import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure

namespace InteractiveConsistency.OralAlgorithm

theorem record_of_nonfaulty {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) (hNP : N ⊆ P) (hN : P.card ≤ N.card + m)
    (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ)
    (p q : α) (hp : p ∈ N) (hq : q ∈ N) :
    StepOne m P (fun w => σ (p :: w)) q ∧
      record m P (fun w => σ (p :: w)) q = some (σ [q]) := by sorry

end InteractiveConsistency.OralAlgorithm

