import Mathlib

namespace NonmonotoneSubmod.Shared

/-- The optimum `OPT = max_{S ⊆ X} f(S)` (Feige–Mirrokni–Vondrák 2011, Theorem 2.1, p. 1137):
the maximum of `f` over all `2^|X|` subsets of the finite ground set `X`. The family of subsets
always contains `∅`, so the maximum is taken over a nonempty finite family. -/
def OPT {X : Type} [Fintype X] (f : Finset X → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

end NonmonotoneSubmod.Shared
