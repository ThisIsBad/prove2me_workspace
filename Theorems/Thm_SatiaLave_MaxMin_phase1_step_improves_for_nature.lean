import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proof of Proposition 4, pp. 731–732: an iteration of Phase 1 after which the stopping test
fails lowers the present value of `A` in no state and strictly lowers it in at least one. -/
theorem phase1_step_improves_for_nature {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M)
    (hstep : IsPhase1Step M A P P') (hnot : ¬ Phase1Stops M A P P') :
    (∀ i, presentValue M A P' i ≤ presentValue M A P i) ∧
      ∃ i, presentValue M A P' i < presentValue M A P i := by sorry

end SatiaLave.MaxMin
