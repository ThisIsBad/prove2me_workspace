import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem prop_2_step1_best_response (P : Params) (hP : P.Standing) (σ : Profile P.M)
    (hσ : P.IsSPE 0 σ) (j : Fin P.M)
    (hj : ∀ n, n < P.N → σ j (pathHist σ n) = P.qlo / P.N) :
    ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N := by sorry

end AssemblyCoord.Feedback

