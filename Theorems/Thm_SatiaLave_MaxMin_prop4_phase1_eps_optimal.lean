import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proposition 4, p. 731: along every run `P 0, P 1, …` of Phase 1 for a policy `A`, for every
`ε > 0` there is an iteration from which on nature's present value is within `ε` of nature's
optimum `robustValue M A` in every state; moreover, if the stopping test fires at an
iteration, nature's choice there is exactly optimal. -/
theorem prop4_phase1_eps_optimal {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : ℕ → Sel M)
    (hrun : ∀ n, IsPhase1Step M A (P n) (P (n + 1))) :
    (∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ i, presentValue M A (P m) i ≤ robustValue M A i + ε) ∧
      ∀ n, Phase1Stops M A (P n) (P (n + 1)) → ∀ i, presentValue M A (P n) i = robustValue M A i := by sorry

end SatiaLave.MaxMin
