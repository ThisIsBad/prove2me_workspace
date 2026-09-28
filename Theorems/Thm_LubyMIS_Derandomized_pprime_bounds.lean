import Mathlib

namespace LubyMIS.Derandomized

/-- The bounds on the modified probabilities (Luby 1986, §4.4, p. 1046): for a prime `n ≤ q ≤ 2n`
and a degree `1 ≤ d < n/16`, `p = 1/(2d)` and `p′ = ⌊p·q⌋/q` satisfy `(8/9) p ≤ p′ ≤ p`. -/
theorem pprime_bounds (n q d : ℕ) (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (hd : 1 ≤ d)
    (h16 : 16 * d < n) :
    8 / 9 * (1 / (2 * (d : ℝ))) ≤ ((q / (2 * d) : ℕ) : ℝ) / q ∧
      ((q / (2 * d) : ℕ) : ℝ) / q ≤ 1 / (2 * (d : ℝ)) := by sorry

end LubyMIS.Derandomized
