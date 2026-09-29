import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

/-- Lemma 3.1 (Feige–Mirrokni–Vondrák 2011, p. 1140): for a submodular `f`, if `S` is a local
optimum of `f` and `T ⊆ S` or `T ⊇ S`, then `f(T) ≤ f(S)`. -/
theorem lemma_3_1_local_optimum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (hS : IsLocalOptimum f S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ f S := by sorry

end NonmonotoneSubmod.LocalSearch
