import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

theorem subscenario_consistent {α V : Type*} [DecidableEq α] (P N : Finset α) (m' : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + (m' + 1))
    (σ : List α → V) (hσ : ConsistentUpTo P N (m' + 2) σ)
    (q : α) (hqP : q ∈ P) (hqN : q ∉ N) :
    N ⊆ P.erase q ∧ (P.erase q).card ≤ N.card + m' ∧
      ConsistentUpTo (P.erase q) N (m' + 1) (fun w => σ (w ++ [q])) := by sorry

end InteractiveConsistency.OralAlgorithm

