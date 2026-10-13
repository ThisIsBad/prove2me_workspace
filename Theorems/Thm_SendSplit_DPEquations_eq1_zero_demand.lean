import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

theorem eq1_zero_demand {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I) (hrI : demandSum r I = 0)
    (j : Fin n) (hj : j ∈ I) :
    minCost A c r i I = minCost A c r j (I.erase j) := by sorry

end SendSplit.DPEquations

