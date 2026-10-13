import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality

namespace BertsekasShreve.Generalized

open Filter Topology

/-- Proposition 6.3(a), p. 96. Under A.1–A.4 and the exact selection assumption, a uniformly
`N`-stage optimal policy exists if and only if the infimum in
`T^{k+1}(J₀)(x) = inf_{u ∈ U(x)} H[x, u, T^k(J₀)]` is attained for each `x ∈ S` and
`k = 0, 1, …, N − 1`. `N` is a positive integer (p. 28). -/
theorem prop6_3a_uniform_optimal_iff_attained {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hES : P.ExactSelection)
    (N : ℕ) (hN : 0 < N) :
    (∃ π : P.Policy, P.IsUniformlyNStageOptimal N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ P.U x, P.H x u (P.T^[k] P.J0) = P.T^[k + 1] P.J0 x := by sorry

end BertsekasShreve.Generalized

