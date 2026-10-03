import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.4 (Reward Iteration; Bäuerle–Rieder, p. 20, PDF 35), under the standing
Integrability Assumption (AN) of Section 2.2. Let `π = (f_0,…,f_{N-1})` be
an `N`-stage policy. For `n = 0,…,N-1` it holds: a) `V_N^π = g_N` and
`V_n^π = T_n^{f_n} V_{n+1}^π`; b) `V_n^π = T_n^{f_n} ⋯ T_{N-1}^{f_{N-1}} g_N`. -/
theorem reward_iteration {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M) (π : Policy M) :
    (∀ x, Vpi M π N x = (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, Vpi M π n x = Tf M n (Vpi M π (n + 1)) (π.1 n) x) ∧
    (∀ n ≤ N, ∀ x, Vpi M π n x = TfChain M π (N - n) n (fun x => (M.g x : EReal)) x) := by sorry

end MDPFinance.Bellman
