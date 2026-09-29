import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proposition 3, p. 731: if the algorithm terminates at `A` (Phase 2 returns `A` itself), no
pure stationary policy has a higher max-min return than `A` in any state. -/
theorem prop3_no_better_policy_undetected {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : Policy S D) (hterm : IsPhase2Step M A A) :
    ∀ (B : Policy S D) (i : S), robustValue M B i ≤ robustValue M A i := by sorry

end SatiaLave.MaxMin
