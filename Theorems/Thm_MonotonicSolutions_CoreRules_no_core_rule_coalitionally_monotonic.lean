import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoreRule
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic

namespace MonotonicSolutions.CoreRules

theorem no_core_rule_coalitionally_monotonic (n : ℕ) (hn : 5 ≤ n) :
    ¬ ∃ φ : Game n → Fin n → ℝ,
      IsAllocationProcedure φ ∧ IsCoreRule φ ∧ IsCoalitionallyMonotonic φ := by sorry

end MonotonicSolutions.CoreRules

