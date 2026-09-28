import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, proof of Theorem 3.4, p. 1141, last paragraph:
`OPT ≤ n f({v})` for a singleton `{v}` of maximum value, for a nonnegative submodular `f` on a
ground set of `n = |X| ≥ 2` elements. -/
theorem opt_le_card_mul_max_singleton {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hn : 2 ≤ Fintype.card X) (v : X) (hv : IsMaxSingleton f v) :
    NonmonotoneSubmod.Shared.OPT f ≤ (Fintype.card X : ℝ) * f {v} := by sorry

end NonmonotoneSubmod.LocalSearch
