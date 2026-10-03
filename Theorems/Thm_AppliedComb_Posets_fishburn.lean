import Mathlib
import Definitions.Def_AppliedComb_Posets_intervalOrder

namespace AppliedComb.Posets

/-- Theorem 6.29 (Fishburn's Theorem), Keller & Trotter p. 129: a finite poset is an interval
order if and only if it excludes `2 + 2`. -/
theorem fishburn (α : Type*) [PartialOrder α] [Fintype α] :
    IsIntervalOrder α ↔ Excludes α TwoPlusTwo := by sorry

end AppliedComb.Posets

