import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

namespace GilmoreGomoryTSP.MinCost

theorem lemma_7_graphStar_connected {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1)))
    (hψ : IsTour ψ) : (graphStar φ ψ).Connected := by sorry

end GilmoreGomoryTSP.MinCost

