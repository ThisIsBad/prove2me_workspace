import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Finite oscillation seminorm (1.13), expressed by pairwise differences
inside each component, never across separate components. -/
def ComponentHolder {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (μ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContinuousOn f Ω ∧ ∃ ρ₀ M : ℝ, 0 < ρ₀ ∧ 0 ≤ M ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ x z : EuclideanSpace ℝ (Fin d),
      z ∈ Ω ∩ Metric.ball x ρ →
      ∀ y ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z,
      ∀ w ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z,
        |f y - f w| ≤ M * ρ ^ μ

end EthierKurtz
