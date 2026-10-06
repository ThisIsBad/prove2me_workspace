import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Algorithm

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- p. 389: the constraints of (26) are a subset of those of (25), and the algorithm's stopping
rule is correct. For every set `I` of identified pairs:
1. every `(x, χ, u)` feasible for (25) gives a feasible `(x, u)` for (26) whose objective, after
   the constant `−Σ_i Σ_j p_ij q⁻_ij h_ij` dropped from (26) is restored, is at most the (25)
   objective;
2. if `(x, u)` is optimal for (26) and (27) is violated by no unidentified pair at `x`, then
   `(x, Tx, ũ)` is optimal for (25), where `ũ_l = u_l` for `l ∈ I` and `ũ_l = 0` otherwise. -/
theorem relaxation_stop (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J)) :
    (∀ x χ u, Feasible25 inst x χ u →
      MasterFeasible inst I x (fun l => u l.1 l.2) ∧
      masterObj inst I x (fun l => u l.1 l.2) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j ≤ obj25 inst x χ u) ∧
    ∀ x u, MasterOptimal inst I x u → violated inst I x = ∅ →
      IsOptimal25 inst x (inst.T.mulVec x) (fun i j => if (i, j) ∈ I then u (i, j) else 0) := by sorry

end MulticutLShaped.SimpleRecourse

