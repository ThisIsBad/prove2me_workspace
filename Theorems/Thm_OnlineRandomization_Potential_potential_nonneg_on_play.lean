import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

theorem potential_nonneg_on_play {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ)
    (S : OnlineAdv R A) :
    0 ≤ pexp (behPlay g S) (fun z => Φ z.1 z.2.1 z.2.2) := by sorry

end OnlineRandomization.Potential

