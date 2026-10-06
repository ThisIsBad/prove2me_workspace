import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

theorem lemma_3_1_if {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (hα : IsLinear α) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) :
    IsCompetitiveOnlineBeh F α g := by sorry

end OnlineRandomization.Potential

