import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped

theorem first_return_cut_each {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (s s' : State n1 K) (hstep : Step inst s s') (hempty : ∀ k, s.optCuts k = [])
    (hret : s'.nOpt = s.nOpt + 1) :
    ∀ k, ∃ c ∈ cutSet inst k, s'.optCuts k = [c] := by sorry

end MulticutLShaped.Bound

