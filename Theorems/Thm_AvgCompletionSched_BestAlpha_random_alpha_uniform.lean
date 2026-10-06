import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_uniform {n : ℕ} {I : Instance n} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, w j * P.CP j ≤ ∑ j, w j * P'.CP j)
    (N : NonpreemptiveSchedule I) :
    IntervalIntegrable (fun α => ∑ j, w j * P.Calpha α j) MeasureTheory.volume 0 1 ∧
      ∫ α in (0 : ℝ)..1, ∑ j, w j * P.Calpha α j ≤ 2 * ∑ j, w j * N.C j := by sorry
end AvgCompletionSched.BestAlpha

