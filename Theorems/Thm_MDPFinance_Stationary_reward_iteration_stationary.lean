import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- Theorem 2.5.3 (Reward Iteration) (Bäuerle–Rieder, p. 41, PDF 56), under the standing
Integrability Assumption (AN) for the `N`-stage model, `n ≤ N`. For `π = (f_0, …,
f_{n-1})` it holds: `J_n^π = T^{f_0} … T^{f_{n-1}} g`. -/
theorem reward_iteration_stationary {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : StationaryMarkovDecisionModel E A) (N : ℕ) (hAN : IntegrabilityAssumption M N)
    (π : ℕ → E → A) (n : ℕ) (hn : n ≤ N) (hπ : IsPolicySeq M n π) :
    Jpi M π n = TfComposeChain M π n (fun x => (M.g x : EReal)) := by sorry

end MDPFinance.Stationary
