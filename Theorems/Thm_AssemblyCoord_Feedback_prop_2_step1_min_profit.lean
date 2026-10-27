import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem prop_2_step1_min_profit (P : Params) (hP : P.Standing) (σ : Profile P.M)
    (hpath : ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) :
    ∀ n, n < P.N → ∀ σ' : Profile P.M, P.IsSPE 0 σ' → ∀ i : Fin P.M,
      P.profit (P.final 0 σ (pathHist σ n)) i ≤ P.profit (P.final 0 σ' (pathHist σ n)) i := by sorry

end AssemblyCoord.Feedback

