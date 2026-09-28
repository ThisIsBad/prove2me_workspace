import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, proof of Theorem 3.4, p. 1141, first display: for a
nonnegative submodular `f`, `α ≥ 0`, a `(1 + α)`-approximate local optimum `S` and any set `C`,
`2(1 + nα) f(S) + f(X \ S) ≥ f(C)`, where `n = |X|`. -/
theorem approx_local_opt_vs_any_set {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (C : Finset X) :
    f C ≤ 2 * (1 + (Fintype.card X : ℝ) * α) * f S + f Sᶜ := by sorry

end NonmonotoneSubmod.LocalSearch
