import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- §2.3: for a nonnegative normalized cost function `γ` (`γ(a → b) = δ(γ, a, b)`, §1.1) and
any strings `A, B` (given as 1-based sequences, `A^i = A_1 ⋯ A_i`), every edit matrix entry
`δ_{i,j} = δ(γ, A^i, B^j)` is the minimum cost of an edit path from `(0, 0)` to `(i, j)`. -/
theorem editDist_eq_pathMin {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hnorm : IsNormalized γ) (A B : ℕ → α) (i j : ℕ) :
    editDist γ (List.ofFn fun t : Fin i => A (t.val + 1))
        (List.ofFn fun t : Fin j => B (t.val + 1)) =
      pathMin γ A B (0, 0) (i, j) := by sorry

end MasekPaterson.Necessity

