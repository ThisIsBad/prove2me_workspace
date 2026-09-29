import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_FourRussians_algorithms
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Algorithm Y computes a submatrix's final step vectors (§2.1): for the `(i, j, m)`
submatrix of the edit matrix of `A, B` (upper-left entry `δ_{i,j}`, with `i + m ≤ |A|`,
`j + m ≤ |B|`), Algorithm Y applied to the strings `C = A^{i+1,i+m}`, `D = B^{j+1,j+m}` and
the actual initial step vectors `R = ⟨δ_{i+k,j} − δ_{i+k−1,j}⟩_{k=1..m}` (left column) and
`S = ⟨δ_{i,j+k} − δ_{i,j+k−1}⟩_{k=1..m}` (top row) returns the actual final step vectors
`R' = ⟨δ_{i+k,j+m} − δ_{i+k−1,j+m}⟩_{k=1..m}` (right column) and
`S' = ⟨δ_{i+m,j+k} − δ_{i+m,j+k−1}⟩_{k=1..m}` (bottom row). Vectors are 0-based in Lean:
entry `k : Fin m` is the paper's entry `k + 1`. -/
theorem blockY_final_steps {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j m : ℕ)
    (hiA : i + m ≤ A.length) (hjB : j + m ≤ B.length) :
    blockY γ m
        (fun k => A[i + k.val]) (fun k => B[j + k.val])
        (fun k => dmat γ A B (i + k.val + 1) j - dmat γ A B (i + k.val) j)
        (fun k => dmat γ A B i (j + k.val + 1) - dmat γ A B i (j + k.val)) =
      (fun k => dmat γ A B (i + k.val + 1) (j + m) - dmat γ A B (i + k.val) (j + m),
       fun k => dmat γ A B (i + m) (j + k.val + 1) - dmat γ A B (i + m) (j + k.val)) := by sorry

end MasekPaterson.FourRussians

