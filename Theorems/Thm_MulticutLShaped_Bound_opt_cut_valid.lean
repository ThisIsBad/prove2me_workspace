import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

theorem opt_cut_valid {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K) (k : Fin K)
    (b : Basis n2 m2) (x' : Fin n1 → ℝ) (hb : IsSimplexOptimal inst k b x') :
    (∀ x : Fin n1 → ℝ, (((optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x : ℝ) : EReal) ≤
      (inst.p k : EReal) * QVal inst x k) ∧
    (((optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x' : ℝ) : EReal) =
      (inst.p k : EReal) * QVal inst x' k := by sorry

end MulticutLShaped.Bound

