import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped

theorem new_cut_each_return {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (s s' : State n1 K) (hstep : Step inst s s') (hret : s'.nOpt = s.nOpt + 1) :
    (∀ k, s'.optCuts k = s.optCuts k ∨
      ∃ c ∈ cutSet inst k, c ∉ s.optCuts k ∧ s'.optCuts k = s.optCuts k ++ [c]) ∧
    ∃ k, ∃ c ∈ cutSet inst k, c ∉ s.optCuts k ∧ s'.optCuts k = s.optCuts k ++ [c] := by sorry

end MulticutLShaped.Bound

