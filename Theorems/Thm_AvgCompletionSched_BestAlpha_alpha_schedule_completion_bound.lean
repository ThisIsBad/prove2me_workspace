import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem alpha_schedule_completion_bound {n : ℕ} {I : Instance n}
    (P : PreemptiveSchedule I) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (π : Fin n ≃ Fin n) (hπ : IsAlphaOrder P α π) (i : Fin n) :
    listCompletion I π i ≤
      P.idle i + (1 + α) * ∑ j ∈ Finset.univ.filter (fun j => α ≤ P.frac i j), I.p j
        + ∑ j ∈ Finset.univ.filter (fun j => P.frac i j < α), P.frac i j * I.p j := by sorry
end AvgCompletionSched.BestAlpha

