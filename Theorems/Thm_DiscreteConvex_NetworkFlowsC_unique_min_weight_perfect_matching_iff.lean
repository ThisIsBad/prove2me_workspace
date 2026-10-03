import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsMinWeightMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValue

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Proposition 9.24 (p.266). A bipartite weighted graph has a unique minimum-weight perfect
matching iff there is a potential and orderings of the two vertex classes satisfying the
displayed sign pattern (Eq. (9.77)). The minimum weight must be finite: the book's condition is
about matchings of the graph, and a single matching of weight `+∞` would otherwise be a unique
minimum while the right side needs `+∞ + p̂(u) - p̂(v) = 0`. -/
theorem unique_min_weight_perfect_matching_iff (Vp Vn : Finset V) (m : ℕ) (hVp : Vp.card = m)
    (hVn : Vn.card = m) (c : V → V → WithTop ℝ) :
    ((∃! M, IsMinWeightMatching Vp Vn c M) ∧ MinWeightValue Vp Vn c ≠ ⊤) ↔
    ∃ (phat : V → ℝ) (ordU ordV : Fin m → V), (∀ i, ordU i ∈ Vp) ∧ (∀ i, ordV i ∈ Vn) ∧
      Function.Injective ordU ∧ Function.Injective ordV ∧
      ∀ i j : Fin m,
        (i = j → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) = 0) ∧
        ((j:ℕ) < (i:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) ≥ 0) ∧
        ((i:ℕ) < (j:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) > 0) := by sorry

end DiscreteConvex.NetworkFlowsC
