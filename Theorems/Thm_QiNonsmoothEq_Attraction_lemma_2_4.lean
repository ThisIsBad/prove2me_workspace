import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, Lemma 2.4, p. 232: if the locally Lipschitz `F : ℝⁿ → ℝᵐ` is BD-regular at `x`,
there is a constant `c` with `‖h‖ ≤ c ‖F'(x; h)‖` for every `h` (2.11). -/
theorem lemma_2_4 {n m : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hreg : BDRegularAt F x) :
    ∃ c : ℝ, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F x h‖ := by sorry

end QiNonsmoothEq.Attraction

