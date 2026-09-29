import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Theorem 1 [Wagner–Fischer]: `δ_{0,0} = 0`, `δ_{i,0} = ∑_{1≤r≤i} D_{A_r}` for
`1 ≤ i ≤ |A|`, and `δ_{0,j} = ∑_{1≤r≤j} I_{B_r}` for `1 ≤ j ≤ |B|`, for a nonnegative
normalized cost function. -/
theorem initial_vectors {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) :
    dmat γ A B 0 0 = 0 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ A.length → dmat γ A B i 0 = ((A.take i).map (delCost γ)).sum) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ B.length → dmat γ A B 0 j = ((B.take j).map (insCost γ)).sum) := by sorry

end MasekPaterson.FourRussians

