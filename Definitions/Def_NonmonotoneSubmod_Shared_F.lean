import Mathlib

namespace NonmonotoneSubmod.Shared

/-- The expectation of `f` on an independently sampled random subset (the multilinear extension,
Feige–Mirrokni–Vondrák 2011, p. 1142): element `i` is included independently with probability
`x i`, and `F f x = E[f(R)] = ∑_{S ⊆ X} f(S) ∏_{i ∈ S} x_i ∏_{i ∉ S} (1 - x_i)`.
The random set `X(p)` of p. 1137 corresponds to `x = fun _ => p`. -/
def F {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (x : X → ℝ) : ℝ :=
  ∑ S : Finset X, f S * ∏ i : X, (if i ∈ S then x i else 1 - x i)

end NonmonotoneSubmod.Shared
