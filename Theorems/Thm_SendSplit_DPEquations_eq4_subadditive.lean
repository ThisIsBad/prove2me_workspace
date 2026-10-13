import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

theorem eq4_subadditive {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I)
    (x y : Fin n → Fin n → ℝ) (hx : IsPreflow A x) (hy : IsPreflow A y)
    (hxy : IsFlow A (subDemand r i I) (x + y)) :
    minCost A c r i I ≤ ((flowCost A c x + flowCost A c y : ℝ) : EReal) := by sorry

end SendSplit.DPEquations

