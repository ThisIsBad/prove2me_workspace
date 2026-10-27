import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

theorem theorem_2_quasiconcavity {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε) (α : N → ℝ)
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) (i : N) :
    (ContinuousOn (fun a => smSpend P ε (Function.update α i a) i) (Set.Icc 0 1) ∧
      StrictMonoOn (fun a => smSpend P ε (Function.update α i a) i) (Set.Icc 0 1)) ∧
    StrictMonoOn (fun a => smUtility P ε H (Function.update α i a) i)
      {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ smSpend P ε (Function.update α i a) i ≤ P.B i} ∧
    ((∀ k, ∑ j, P.v k j + 2 * ε ≤ M) → M / ε < H →
      StrictAntiOn (fun a => smUtility P ε H (Function.update α i a) i)
        {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ P.B i ≤ smSpend P ε (Function.update α i a) i}) := by sorry

end MultPacing.Existence

