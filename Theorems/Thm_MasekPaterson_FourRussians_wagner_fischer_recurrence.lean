import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Theorem 2 [Wagner–Fischer]: for `1 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|`,
`δ_{i,j} = min(δ_{i−1,j−1} + R_{A_i,B_j}, δ_{i−1,j} + D_{A_i}, δ_{i,j−1} + I_{B_j})`,
for a nonnegative normalized cost function. `A_i` (1-based) is `A[i-1]`. -/
theorem wagner_fischer_recurrence {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    dmat γ A B i j =
      min (min (dmat γ A B (i - 1) (j - 1) + replCost γ A[i - 1] B[j - 1])
               (dmat γ A B (i - 1) j + delCost γ A[i - 1]))
          (dmat γ A B i (j - 1) + insCost γ B[j - 1]) := by sorry

end MasekPaterson.FourRussians

