import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem proposition_2_i (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M) :
    (∃ σ : Profile P.M, P.IsSPSE 0 σ ∧
        ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
    (∀ σ : Profile P.M, P.IsSPSE 0 σ →
        (∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
        projectLevel (P.final 0 σ []) = P.qlo) := by sorry

end AssemblyCoord.Feedback

