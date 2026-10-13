import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem
import Definitions.Def_SendSplit_DPEquations_Equations

namespace SendSplit.DPEquations

theorem eq5_send_le {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i j : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I)
    (hij : IsSendArc A r I i j) :
    minCost A c r i I ≤ sendCost A c r I i j + minCost A c r j I := by sorry

end SendSplit.DPEquations

