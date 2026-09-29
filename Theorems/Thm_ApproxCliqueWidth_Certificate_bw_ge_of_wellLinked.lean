import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Theorem 5.1 (p. 519), with the misprint for `k = 1` corrected by the hypothesis
`k ≠ 1`: every branch-decomposition of `f` has an edge of width at least `k / 3`. -/
theorem bw_ge_of_wellLinked {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (f : Finset V → ℤ) (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    (h0 : f ∅ = 0) (k : ℕ) (hk : k ≠ 1) (W : Finset V) (hWcard : W.card = k)
    (hW : IsWellLinked f W) :
    ∀ D : BranchDecomp V, ∃ u w : Fin D.n, D.T.Adj u w ∧ (k : ℤ) ≤ 3 * f (D.side u w) := by sorry

end ApproxCliqueWidth.Certificate
