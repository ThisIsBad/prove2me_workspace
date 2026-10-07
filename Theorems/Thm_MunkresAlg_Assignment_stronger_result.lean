import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, the stronger result, p. 35: if the Step 3 transformation from `A_k = s.A` to
`A_{k+1} = s₁.A` leaves the maximal number of independent zeros unchanged, then every way of
continuing Step 1 from `s₁` until Step 1 is left goes to Step 3 (Step 2 does not occur), and
Step 3 is begun with more covered rows (horizontal lines) than at `s`, every covered row of `s`
still being covered. -/
theorem stronger_result {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s s₁ : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) (h1 : Step s s₁)
    (heq : maxIndepZeros s₁.A = maxIndepZeros s.A) :
    ∀ s₂ : State n, Relation.ReflTransGen Step1Move s₁ s₂ → s₂.phase ≠ Phase.step1 →
      s₂.phase = Phase.step3 ∧ s.rowCov ⊆ s₂.rowCov ∧ s.rowCov.card < s₂.rowCov.card := by sorry

end MunkresAlg.Assignment

