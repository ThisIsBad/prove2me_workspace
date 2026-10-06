import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

open MeasureTheory

theorem competitive_against_H {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (hα : IsLinear α) (g : BehAlg R A)
    (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω)
    (M : DetAlg R A) (hM : ObeysPotentialRule Φ H M) (r : List R) :
    M.costOn F r ≤ ∫ y, α ((H.alg y).costOn F r) ∂H.μ := by sorry

end OnlineRandomization.Potential

