import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist

namespace MasekPaterson.Shared

variable {α : Type*}

/-- The set of possible steps for the cost function `γ`: every difference between two
vertically adjacent entries, `δ_{i,j} - δ_{i-1,j}` (`1 ≤ i ≤ |A|`, `0 ≤ j ≤ |B|`), or two
horizontally adjacent entries, `δ_{i,j} - δ_{i,j-1}` (`0 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|`), of the
edit matrix of some pair of strings `A, B` over the alphabet. -/
def possibleSteps (γ : EditOp α → ℝ) : Set ℝ :=
  {s : ℝ | ∃ (A B : List α) (i j : ℕ),
    (1 ≤ i ∧ i ≤ A.length ∧ j ≤ B.length ∧ s = dmat γ A B i j - dmat γ A B (i - 1) j) ∨
    (i ≤ A.length ∧ 1 ≤ j ∧ j ≤ B.length ∧ s = dmat γ A B i j - dmat γ A B i (j - 1))}

/-- `Ω = {D_a | a ∈ Σ} ∪ {I_a | a ∈ Σ} ∪ {R_{a,b} | a, b ∈ Σ}`, the set of edit costs. -/
def costSet (γ : EditOp α → ℝ) : Set ℝ :=
  {x | ∃ a, x = delCost γ a} ∪ {x | ∃ a, x = insCost γ a} ∪ {x | ∃ a b, x = replCost γ a b}

/-- `Ω` is discrete: there is a constant `r > 0` such that every element of `Ω` is an
integral multiple of `r`. -/
def IsDiscrete (γ : EditOp α → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ ω ∈ costSet γ, ∃ z : ℤ, ω = z * r

end MasekPaterson.Shared
