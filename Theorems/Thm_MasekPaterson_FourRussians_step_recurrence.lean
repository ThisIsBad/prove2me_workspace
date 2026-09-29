import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Corollary 1 (of Theorem 2): the Wagner–Fischer recurrence in terms of steps. For
`1 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|` and a nonnegative normalized cost function,
`δ_{i,j} − δ_{i−1,j} = min{R_{A_i,B_j} − (δ_{i−1,j} − δ_{i−1,j−1}), D_{A_i},
  I_{B_j} + (δ_{i,j−1} − δ_{i−1,j−1}) − (δ_{i−1,j} − δ_{i−1,j−1})}` and
`δ_{i,j} − δ_{i,j−1} = min{R_{A_i,B_j} − (δ_{i,j−1} − δ_{i−1,j−1}),
  D_{A_i} + (δ_{i−1,j} − δ_{i−1,j−1}) − (δ_{i,j−1} − δ_{i−1,j−1}), I_{B_j}}`. -/
theorem step_recurrence {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    dmat γ A B i j - dmat γ A B (i - 1) j =
      min (min (replCost γ A[i - 1] B[j - 1]
                  - (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1)))
               (delCost γ A[i - 1]))
          (insCost γ B[j - 1] + (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1))
                  - (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1))) ∧
    dmat γ A B i j - dmat γ A B i (j - 1) =
      min (min (replCost γ A[i - 1] B[j - 1]
                  - (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1)))
               (delCost γ A[i - 1] + (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1))
                  - (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1))))
          (insCost γ B[j - 1]) := by sorry

end MasekPaterson.FourRussians

