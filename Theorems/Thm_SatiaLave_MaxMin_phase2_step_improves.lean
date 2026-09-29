import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proof of Proposition 5, p. 732: if Phase 2 changes the policy from `A` to `B ≠ A`, the
max-min return of `B` is at least that of `A` in every state and strictly larger in at least
one. -/
theorem phase2_step_improves {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A B : Policy S D) (hstep : IsPhase2Step M A B) (hne : B ≠ A) :
    (∀ i, robustValue M A i ≤ robustValue M B i) ∧ ∃ i, robustValue M A i < robustValue M B i := by sorry

end SatiaLave.MaxMin
