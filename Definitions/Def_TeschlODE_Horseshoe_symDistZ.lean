import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §11.5, p. 306, (11.35): the metric on the two-sided space `Σ_N = {0, …, N − 1}^ℤ`,
`d(x, y) = ½ ∑_{n ∈ ℕ₀} (|xₙ − yₙ| + |x₋ₙ − y₋ₙ|) / Nⁿ`. For `N ≥ 2` the series converges,
being bounded termwise by `2(N − 1)/Nⁿ`. -/
noncomputable def symDistZ (N : ℕ) (x y : ℤ → Fin N) : ℝ :=
  1 / 2 * ∑' n : ℕ,
    (|((x n : ℕ) : ℝ) - ((y n : ℕ) : ℝ)| + |((x (-(n : ℤ)) : ℕ) : ℝ) - ((y (-(n : ℤ)) : ℕ) : ℝ)|) /
      (N : ℝ) ^ n

end TeschlODE.Horseshoe
