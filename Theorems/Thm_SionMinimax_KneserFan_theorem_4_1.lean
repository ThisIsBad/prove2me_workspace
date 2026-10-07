import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_1 {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, (c : EReal) < infSup f →
      ∃ X : Finset M, ∀ ν : N, ∃ x ∈ X, c < f x ν) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan

