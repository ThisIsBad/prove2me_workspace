import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

theorem theorem_3_1 {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α β : ℝ → ℝ) (hα : IsLinear α) (hα_mono : Monotone α)
    (hβ : IsLinear β) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (hH : IsCompetitiveObl F β H) :
    (∃ M : DetAlg R A, ObeysPotentialRule Φ H M) ∧
      ∀ M : DetAlg R A, ObeysPotentialRule Φ H M → IsCompetitive F (α ∘ β) M := by sorry

end OnlineRandomization.Potential

