import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.5, p. 302, (11.28) (and (11.24) for `N = 2`): the metric on
`Σ_N = {0, …, N − 1}^{ℕ₀}`, `d(x, y) = ∑_{n ∈ ℕ₀} |xₙ − yₙ| / Nⁿ`. For `N ≥ 2` (the book's
`N ∈ ℕ \ {1}`) the series converges, being bounded termwise by `(N − 1)/Nⁿ`. -/
noncomputable def symDist (N : ℕ) (x y : ℕ → Fin N) : ℝ :=
  ∑' n : ℕ, |((x n : ℕ) : ℝ) - ((y n : ℕ) : ℝ)| / (N : ℝ) ^ n

end TeschlODE.Shared
