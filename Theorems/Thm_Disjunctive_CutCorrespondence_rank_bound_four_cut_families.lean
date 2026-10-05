import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau
import Definitions.Def_Disjunctive_CutCorrespondence_Rank

namespace Disjunctive.CutCorrespondence

/-- Theorem 8.7 (Balas §8.4, p. 105), the goal theorem of this mission: the rank of `P` (the LP
relaxation) with respect to each of (a) unstrengthened lift-and-project cuts, (b) simple
disjunctive cuts, (c) strengthened lift-and-project cuts, and (d) mixed integer Gomory cuts
(equivalently, strengthened simple disjunctive cuts) is at most `p := |N'|`, the number of 0-1
variables. Parts (b)-(d) read the cuts off the simplex tableau of `Ã`, so the bound rows
`0 ≤ x_j ≤ 1`, `j ∈ N'`, must be part of the system: for `P = [-1,2]` in one variable with
`N' = {0}` no basis has `0 < ā_{k0} < 1`, the simple disjunctive closure is `P` itself, and
`conv(K₀) = [0,1]` is strictly smaller. -/
theorem rank_bound_four_cut_families {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n))
    (hbounds : Poly A b ⊆ {x | ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1}) :
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card := by sorry

end Disjunctive.CutCorrespondence

