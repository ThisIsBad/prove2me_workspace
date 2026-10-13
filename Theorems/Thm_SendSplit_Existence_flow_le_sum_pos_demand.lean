import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem flow_le_sum_pos_demand {n : ℕ} (G : ArcGraph n) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) (p : Fin n × Fin n) (hp : p ∈ G.A)
    (hpC : ¬ SameComponent G p.1 p.2) :
    x p.1 p.2 ≤ ∑ i, max (r i) 0 := by sorry

end SendSplit.Existence

