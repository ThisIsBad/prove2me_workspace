import Mathlib

namespace MNLBandit.UCB

open MeasureTheory ProbabilityTheory

theorem theorem_5 (n : ℕ) (hn : 1 ≤ n) (p : unitInterval) (hp : p ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let μ : ℝ := (1 - (p : ℝ)) / (p : ℝ)
    let P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p)
    let Xbar : (Fin n → ℕ) → ℝ := fun x => (∑ k, (x k : ℝ)) / (n : ℝ)
    (μ ≤ 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * μ * δ ^ 2) / (2 * (1 + δ) * (1 + μ) ^ 2)))) ∧
    (1 ≤ μ → δ < 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2 / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (μ ≤ 1 → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (1 ≤ μ → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2) / (2 * (1 + μ) ^ 2)))) := by sorry

end MNLBandit.UCB

