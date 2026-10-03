import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_BinomialPower

namespace MDPFinance.TerminalWealth

/-- Lemma 4.2.9 (Bäuerle–Rieder, p. 86, PDF 100). Consider the binomial model with power
utility and parameter `γ < 1`, `γ ≠ 0`, up factor `u`, down factor `down` (`down < 1+i < u`),
up-probability `p ∈ (0,1)`. a) The optimal fraction `α*` invested in the stock is given by (4.9)
(`binomialAlphaStar`): for `0 < γ < 1` it maximizes the one-period objective on `[α_0,α_1]`, and
for `γ < 0` it minimizes it on `(α_0,α_1)` (problem (4.8), Remark 4.2.7). b) `α* = α*(p)` is
increasing in `p`. c) If `p = (1+i-down)/(u-down)` then `α*(p) = 0`. -/
theorem binomial_power_utility_monotone (i u down γ : ℝ) (hγ1 : γ < 1) (hγ0 : γ ≠ 0)
    (hdown : down < 1 + i) (hu : 1 + i < u) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1,
        (0 < γ → IsMaxOn (binomialObjective i u down γ p)
          (Set.Icc (binomialAlpha0 i u) (binomialAlpha1 i down)) (binomialAlphaStar i u down γ p)) ∧
        (γ < 0 → IsMinOn (binomialObjective i u down γ p)
          (Set.Ioo (binomialAlpha0 i u) (binomialAlpha1 i down))
          (binomialAlphaStar i u down γ p))) ∧
      MonotoneOn (binomialAlphaStar i u down γ) (Set.Ioo (0 : ℝ) 1) ∧
      binomialAlphaStar i u down γ ((1 + i - down) / (u - down)) = 0 := by sorry

end MDPFinance.TerminalWealth
