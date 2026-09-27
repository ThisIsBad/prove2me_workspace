import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

/-- **Theorem 9.2 (Chernoff bounds)** (p. 190). Let `X₁, …, Xₘ` be independent Bernoulli trials
with success probability `p` and `S = X₁ + ⋯ + Xₘ`, so `E[S] = pm`. Then for `0 < γ ≤ 1`:
(additive form) `Pr[S ≥ (p + γ)m] ≤ e^{−2mγ²}` and `Pr[S ≤ (p − γ)m] ≤ e^{−2mγ²}`;
(multiplicative form) `Pr[S ≥ (1 + γ)pm] ≤ e^{−mpγ²/3}` and `Pr[S ≤ (1 − γ)pm] ≤ e^{−mpγ²/2}`. -/
theorem chernoff_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    trialsLaw p m {ω | (p + γ) * m ≤ successes ω} ≤ ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (p - γ) * m} ≤
      ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (1 + γ) * p * m ≤ successes ω} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 3))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (1 - γ) * p * m} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 2))) := by sorry

end ComputationalLearning

