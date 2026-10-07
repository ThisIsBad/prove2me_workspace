import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- Routine step (3): a nonbasic surplus variable prices out exactly for negative multiplier. -/
theorem step3_slack_test {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (i : Fin m) (hi : Sum.inr i ∉ Set.range β) :
    (Improves I β (Sum.inr i) → mult I β i < 0) ∧
    (IsNondegenerate I β → mult I β i < 0 → Improves I β (Sum.inr i)) := by sorry

end GilmoreGomory61.CuttingStock

