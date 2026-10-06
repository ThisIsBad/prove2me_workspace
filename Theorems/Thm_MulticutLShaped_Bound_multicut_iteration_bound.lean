import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped

theorem multicut_iteration_bound {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (M : ℕ) (hM : 1 ≤ M) (hcut : ∀ k, (cutSet inst k).card ≤ M)
    (s : State n1 K) (hs : Reachable inst s) :
    s.nOpt ≤ 1 + K * (M - 1) := by sorry

end MulticutLShaped.Bound

