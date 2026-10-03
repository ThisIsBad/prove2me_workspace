import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.7 (Verification Theorem; Bäuerle–Rieder, p. 22, PDF 37), under the standing
Integrability Assumption (AN). Let `(v_n) ⊆ IM(E)`,
`n = 0,…,N`, be a solution of the Bellman equation (`v_N = g_N`, `v_n = T_n v_{n+1}` for
`n = 0,…,N-1`). Then a) `v_n ≥ V_n` for `n = 0,…,N`. b) If `f_n^*` is a maximizer of `v_{n+1}`
for `n = 0,…,N-1`, then `v_n = V_n` for every `n`, and the policy
`π^* = (f_0^*,…,f_{N-1}^*)` is optimal for the `N`-stage Markov Decision Problem. -/
theorem verification_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (v : ℕ → E → EReal) (hv_IM : ∀ n, v n ∈ IM E)
    (hv_N : v N = fun x => (M.g x : EReal)) (hv_bellman : ∀ n < N, v n = T M n (v (n + 1))) :
    (∀ n ≤ N, ∀ x, V M n x ≤ v n x) ∧
    (∀ fstar : Policy M, (∀ n < N, IsMaximizer M n (v (n + 1)) (fstar.1 n)) →
        (∀ n ≤ N, v n = V M n) ∧ Vpi M fstar 0 = V M 0) := by sorry

end MDPFinance.Bellman
