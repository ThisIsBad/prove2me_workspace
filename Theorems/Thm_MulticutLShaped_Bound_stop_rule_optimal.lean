import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

theorem stop_rule_optimal {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (hp : ∀ k, 0 < inst.p k) (s : State n1 K) (hs : Reachable inst s)
    (x : Fin n1 → ℝ) (θ : Fin K → ℝ) (β : Fin K → Basis n2 m2)
    (hopt : IsMasterOptimal inst s x θ) (hfeas : ∀ k, feasLPValue inst k x = 0)
    (hβ : ∀ k, IsSimplexOptimal inst k (β k) x)
    (hstop : ∀ k, ¬ Cond14 inst s x θ k (β k)) :
    x ∈ K1 inst ∧ x ∈ K2 inst ∧ ∀ x' ∈ K1 inst, x' ∈ K2 inst → obj inst x ≤ obj inst x' := by sorry

end MulticutLShaped.Bound

