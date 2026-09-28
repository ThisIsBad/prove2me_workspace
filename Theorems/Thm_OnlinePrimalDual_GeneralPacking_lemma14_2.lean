import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_harmonicNum

namespace OnlinePrimalDual.GeneralPacking

/-- **Lemma 14.2** (p. 251, PDF p. 162) — the lower bound showing the `log(a(max)/a(min))`
additive term of Theorem 14.1 is necessary. Uses the book's own explicit instance directly
(single constraint `∑_{j=1}^m (m-j+1)y(j) ≤ 1`, so `a(max)/a(min) = m`): `y : ℕ → ℝ` is any
online `B`-competitive algorithm's output on this instance, formalized via `hB_competitive`
("after the `j`th round, the optimal offline value is `1/(m-j+1)`, thus the value ... given by a
`B`-competitive algorithm must be at least `1/(B(m-j+1))`", p. 251) requiring the cumulative
output after each round `j` to meet this ratio. The conclusion is the book's own summed bound,
`∑_{j=1}^m (m-j+1)y(j) ≥ H(m)/B`. -/
theorem lemma14_2 (m : ℕ) (hm : 1 ≤ m) (B : ℝ) (hB : 0 < B) (y : ℕ → ℝ)
    (hy_nonneg : ∀ k, 0 ≤ y k)
    (hB_competitive : ∀ j ∈ Finset.Icc 1 m,
      1 / (B * ((m : ℝ) - j + 1)) ≤ ∑ k ∈ Finset.Icc 1 j, y k) :
    harmonicNum m / B ≤ ∑ j ∈ Finset.Icc 1 m, ((m : ℝ) - j + 1) * y j := by sorry

end OnlinePrimalDual.GeneralPacking
