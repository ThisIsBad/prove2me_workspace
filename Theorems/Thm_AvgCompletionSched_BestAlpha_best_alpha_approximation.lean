import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem best_alpha_approximation {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (hP : ∀ P' : PreemptiveSchedule I, ∑ j, P.CP j ≤ ∑ j, P'.CP j) :
    ∃ α ∈ Set.Ioc (0 : ℝ) 1, ∀ π : Fin n ≃ Fin n, IsAlphaOrder P α π →
      ∀ N : NonpreemptiveSchedule I,
        ∑ j, listCompletion I π j ≤ Real.exp 1 / (Real.exp 1 - 1) * ∑ j, N.C j := by sorry
end AvgCompletionSched.BestAlpha

