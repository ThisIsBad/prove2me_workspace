import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem lemma_OA2_i (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M)
    (q0 : Fin P.M → ℝ)
    (htie : ∃ S : Finset (Fin P.M), P.N + 1 ≤ S.card ∧ ∀ i ∈ S, ∀ j, q0 i ≤ q0 j) :
    ∃ σ : Profile P.M, P.IsSPE q0 σ ∧
      ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N := by sorry

end AssemblyCoord.Feedback

