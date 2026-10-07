import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_2_prime {M N : Type*} [TopologicalSpace N] [CompactSpace N]
    (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hlsc : ∀ μ : M, LowerSemicontinuous (fun ν : N => f μ ν)) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan

