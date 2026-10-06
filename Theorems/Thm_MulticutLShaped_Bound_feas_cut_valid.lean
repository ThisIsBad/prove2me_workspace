import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

theorem feas_cut_valid {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (hp : ∀ k, 0 < inst.p k) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔ ∀ (k : Fin K) (b : FeasBasis n2 m2) (x' : Fin n1 → ℝ),
      IsFeasSimplexOptimal inst k b x' →
        (feasCutCoeffs inst k b).2 ≤ (feasCutCoeffs inst k b).1 ⬝ᵥ x := by sorry

end MulticutLShaped.Bound

