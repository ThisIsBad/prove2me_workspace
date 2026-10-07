import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem exists_permutation_le_B_of_doublyStochastic_le
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) (x : N → ℝ) (D : Matrix N N ℝ)
    (hD : D ∈ doublyStochastic ℝ N)
    (hDB : ∀ i j, D i j ≤ acceptableMatrix A Finset.univ x i j) :
    ∃ P : Matrix N N ℝ, IsSPermutation Finset.univ P ∧
      ∀ i j, P i j ≤ acceptableMatrix A Finset.univ x i j := by sorry

end ShapleyScarf.Balanced

