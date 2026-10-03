import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_AppliedComb_Posets_chainPartition

namespace AppliedComb.Posets

/-- Theorem 6.17 (Dilworth's Theorem), Keller & Trotter p. 122: a finite poset of width `w`
has a partition into `w` chains, and every chain partition has at least `w` parts. -/
theorem dilworth (α : Type*) [PartialOrder α] [Fintype α] :
    (∃ C : Fin (width α) → Finset α, IsChainPartition C) ∧
    ∀ (k : ℕ) (C : Fin k → Finset α), IsChainPartition C → width α ≤ k := by sorry

end AppliedComb.Posets

