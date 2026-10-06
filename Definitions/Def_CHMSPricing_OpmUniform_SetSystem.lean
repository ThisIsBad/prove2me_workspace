import Mathlib

namespace CHMSPricing.OpmUniform

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

/-- The `k`-uniform matroid on the agents `[n] = Fin n` (§5.2, p. 9): "every set of size at
most `k` is independent". -/
def uniformSystem (n k : ℕ) : SetSystem (Fin n) where
  Feasible S := S.card ≤ k
  feasible_empty := by simp
  feasible_mono := fun _ _ hAB hB => (Finset.card_le_card hAB).trans hB

end CHMSPricing.OpmUniform
