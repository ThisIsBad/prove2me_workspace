import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

theorem step_one_values_agree {α V : Type*} [DecidableEq α] (P N : Finset α) (m : ℕ)
    (hNP : N ⊆ P) (hN : P.card ≤ N.card + m)
    (σ : List α → V) (hσ : ConsistentUpTo P N (m + 1) σ)
    (p p' q : α) (hp : p ∈ N) (hp' : p' ∈ N) (hq : q ∈ P)
    (Q₁ Q₂ : Finset α) (hQ₁ : Q₁ ⊆ P) (hQ₂ : Q₂ ⊆ P)
    (hQ₁card : P.card + m < 2 * Q₁.card) (hQ₂card : P.card + m < 2 * Q₂.card)
    (v v' : V)
    (hv : ∀ w : List α, IsStringOver Q₁ w → w.length ≤ m → σ (p :: (w ++ [q])) = v)
    (hv' : ∀ w : List α, IsStringOver Q₂ w → w.length ≤ m → σ (p' :: (w ++ [q])) = v') :
    v = v' := by sorry

end InteractiveConsistency.OralAlgorithm

