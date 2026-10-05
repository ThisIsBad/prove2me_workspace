import Mathlib
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet
import Definitions.Def_DRCVRP_Covariance_Routing

open MeasureTheory

namespace DRCVRP.Covariance

/-- Theorem 6 (p. 727): for some instance of the distributionally robust CVRP with the
covariance ambiguity set (16) — customers `n`, vehicles `m`, capacity `Q ≥ 0`, risk level
`ε ∈ (0,1)`, box `[q̲, q̄]` with `q̲ ≥ 0`, mean `μ ∈ int [q̲, q̄]` and `Σ ≻ 0` — no deterministic
CVRP instance with the same customers and fleet (capacity `Q' ≥ 0`, demands `q ≥ 0`) has the same
set of feasible route sets. -/
theorem no_deterministic_reformulation :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ),
      0 ≤ Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      Sig.PosDef ∧
      ∀ (Q' : ℝ) (q : Fin n → ℝ), 0 ≤ Q' → (∀ j, 0 ≤ q j) →
        {R : Fin m → List (Fin n) | RVRPFeasible (covarianceSet qlo qhi μ Sig) ε Q R} ≠
          {R | DetFeasible Q' q R} := by sorry

end DRCVRP.Covariance

