import Mathlib

namespace FoundationsRL.Contextual

/-- The Inverse Gap Weighting distribution property (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Definition 4,
p. 50). Given estimated values `fhat : Fin A → ℝ`, an exploration parameter `γ`, and a
greedy action `bstar`, `IsIGW A fhat γ bstar p` asserts that `p` is the distribution
`p(π) = 1 / (λ + 2γ(fhat(bstar) - fhat(π)))` for some normalizing constant `λ ∈ [1, A]`
(guaranteed to exist by the book via a continuity/intermediate-value argument, p. 50) that
makes `p` sum to one, and that `bstar` is indeed a maximizer of `fhat`. -/
structure IsIGW (A : ℕ) (fhat : Fin A → ℝ) (γ : ℝ) (bstar : Fin A) (p : Fin A → ℝ) : Prop where
  greedy : ∀ π, fhat π ≤ fhat bstar
  lam_spec : ∃ lam ∈ Set.Icc (1 : ℝ) (A : ℝ), ∀ π, p π = 1 / (lam + 2 * γ * (fhat bstar - fhat π))
  nonneg : ∀ π, 0 ≤ p π
  sum_one : ∑ π, p π = 1

end FoundationsRL.Contextual
