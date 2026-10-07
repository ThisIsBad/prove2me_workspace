import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_1_prime {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, supInf f < (c : EReal) →
      ∃ Y : Finset N, ∀ μ : M, ∃ y ∈ Y, f μ y < c) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan

