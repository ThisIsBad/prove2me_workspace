import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_ReducedCost

namespace SendSplit.Existence

theorem reducedFlowCost_eq {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (π : Fin n → ℝ) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) :
    reducedFlowCost G c π x = flowCost G c x + ∑ i, π i * r i := by sorry

end SendSplit.Existence

