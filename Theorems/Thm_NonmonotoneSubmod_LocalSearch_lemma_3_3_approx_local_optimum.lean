import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

/-- Lemma 3.3 (Feige–Mirrokni–Vondrák 2011, p. 1141), under the standing assumption of §3 that `f`
is nonnegative: if `S` is a `(1 + α)`-approximate local optimum of a nonnegative submodular `f`
with `α ≥ 0`, then `f(T) ≤ (1 + nα) f(S)` for every `T` with `T ⊆ S` or `T ⊇ S`, where
`n = |X|`. -/
theorem lemma_3_3_approx_local_optimum {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ (1 + (Fintype.card X : ℝ) * α) * f S := by sorry

end NonmonotoneSubmod.LocalSearch

