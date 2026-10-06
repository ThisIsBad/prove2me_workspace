import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

open MeasureTheory

theorem greedy_choice_exists {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω)
    (r : List R) (x : R) (a : List A) (ha : a.length = r.length) :
    ∃ a' : A, (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ := by sorry

end OnlineRandomization.Potential

