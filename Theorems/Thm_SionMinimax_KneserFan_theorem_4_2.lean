import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_2 {M N : Type*} [TopologicalSpace M] [CompactSpace M]
    (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (husc : ∀ ν : N, UpperSemicontinuous (fun μ : M => f μ ν)) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan

