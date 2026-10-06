import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_two_point {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (π₁ π₂ : Fin n ≃ Fin n) (hπ₁ : IsAlphaOrder P 1 π₁) (hπ₂ : IsAlphaOrder P (1 / 2) π₂)
    (N : NonpreemptiveSchedule I) :
    3 / 5 * ∑ j, w j * listCompletion I π₁ j + 2 / 5 * ∑ j, w j * listCompletion I π₂ j
      ≤ 9 / 5 * ∑ j, w j * N.C j := by sorry
end AvgCompletionSched.BestAlpha

