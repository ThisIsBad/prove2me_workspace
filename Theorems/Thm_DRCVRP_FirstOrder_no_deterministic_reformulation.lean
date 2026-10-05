import Mathlib
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_RouteSet

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Theorem 4 (§5.1, p. 726): there is an instance of the distributionally robust CVRP with an
ambiguity set of the form (12) (capacity `Q > 0`, risk level `ε ∈ (0,1)`, support `[qlo, qhi]`
with `qlo ≥ 0`, mean `μ` in the interior of the box, customer subsets `Sfam`, bounds `ν > 0`)
such that no deterministic CVRP instance with the same customers and vehicles (capacity
`Q' ≥ 0`, demands `q' ≥ 0`) has the same set of feasible route sets. -/
theorem no_deterministic_reformulation :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (p : ℕ) (Sfam : Fin p → Finset (Fin n))
      (ν : Fin p → ℝ),
      0 < Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      (∀ l, 0 < ν l) ∧
      ∀ (Q' : ℝ) (q' : Fin n → ℝ), 0 ≤ Q' → (∀ i, 0 ≤ q' i) →
        {R : Fin m → List (Fin n) |
            IsRVRPFeasible (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε Q R} ≠
          {R : Fin m → List (Fin n) | IsDeterministicFeasible Q' q' R} := by sorry

end DRCVRP.FirstOrder

