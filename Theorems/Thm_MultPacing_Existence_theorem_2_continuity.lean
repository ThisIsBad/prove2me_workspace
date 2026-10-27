import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

theorem theorem_2_continuity {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) :
    (∀ i j, ContinuousOn (fun α => smAlloc P ε α i j) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i j, ContinuousOn (fun α => smPay P ε α i j) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i, ContinuousOn (fun α => smUtility P ε H α i) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) := by sorry

end MultPacing.Existence

