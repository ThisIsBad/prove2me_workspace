import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_MDPFinance_Bellman_StructureAssumption

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.8 (Structure Theorem; Bäuerle–Rieder, p. 23, PDF 38), the book's central
finite-horizon result, under the standing Integrability Assumption (AN). Let the Structure
Assumption (SAN) be satisfied by `(IM_n)`, `(Δ_n)`.
Then: a) `V_n ∈ IM_n` and `(V_n)` satisfies the Bellman equation, i.e. `V_N = g_N` and
`V_n(x) = sup_{a ∈ D_n(x)} [r_n(x,a) + ∫ V_{n+1}(x') Q_n(dx'|x,a)]` for `n = 0,…,N-1`;
b) `V_n = T_n T_{n+1} ⋯ T_{N-1} g_N`; c) for `n = 0,…,N-1` there exists a maximizer `f_n` of
`V_{n+1}` with `f_n ∈ Δ_n`, and every sequence of maximizers `f_n^*` of `V_{n+1}` defines an
optimal policy `(f_0^*,…,f_{N-1}^*)` for the `N`-stage Markov Decision Problem. Here `V_n` is
*the* value function `sup_π V_n^π` fixed before this theorem is proved (Def., p. 18, PDF 33),
not an arbitrary object merely postulated to satisfy the Bellman equation — that weaker claim
is Theorem 2.3.7. -/
theorem structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas) :
    (∀ n ≤ N, V M n ∈ IMs n) ∧
    (V M N = fun x => (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, V M n x = ⨆ a ∈ M.Dx n x, (M.r n (x, a) : EReal) + erealIntegral
        (M.Q n (x, a)) (V M (n + 1))) ∧
    (∀ n ≤ N, V M n = TChain M (N - n) n (fun x => (M.g x : EReal))) ∧
    (∀ n < N, ∃ f ∈ Deltas n, IsMaximizer M n (V M (n + 1)) f) ∧
    (∀ fstar : Policy M, (∀ n < N, IsMaximizer M n (V M (n + 1)) (fstar.1 n)) →
        Vpi M fstar 0 = V M 0) := by sorry

end MDPFinance.Bellman
