import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

theorem hat_quorum_step_one {α V : Type*} [DecidableEq α] (P : Finset α) (m' : ℕ)
    (σ : List α → V) (p' q : α) (hqP : q ∈ P)
    (Q : Finset α) (hQP : Q ⊆ P) (hQcard : P.card + (m' + 1) < 2 * Q.card) (v : V)
    (hv : ∀ w : List α, IsStringOver Q w → w.length ≤ m' + 1 → σ (p' :: (w ++ [q])) = v) :
    Q.erase q ⊆ P.erase q ∧
      (P.card + (m' + 1)) / 2 ≤ (Q.erase q).card ∧
      (P.erase q).card + m' < 2 * (Q.erase q).card ∧
      ∀ q' ∈ Q.erase q, ∀ w : List α, IsStringOver (Q.erase q) w → w.length ≤ m' →
        σ (p' :: ((w ++ [q']) ++ [q])) = v := by sorry

end InteractiveConsistency.OralAlgorithm

