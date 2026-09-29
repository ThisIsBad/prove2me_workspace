import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_TwoPointSupport
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

namespace RobustMeanCov.TwoPoint

/-- Lemma 1 (Popescu 2007, p. 102): `u` has two-point support if and only if for every `μ` and
every `σ > 0` there are `a < b` and `q_a, q_b` with
(a) `(b - μ)(μ - a) = σ²`, (b) `(u(b) - u(a)) / (b - a) = (q_a + q_b) / 2`, and
(c) the quadratic `q(y) = A y² + B y + C` with the coefficients of Lemma 1 lies below `u`. -/
theorem lemma1 (u : ℝ → ℝ) :
    TwoPointSupport u ↔
      ∀ μ σ : ℝ, 0 < σ →
        ∃ a b qa qb : ℝ, a < b ∧
          (b - μ) * (μ - a) = σ ^ 2 ∧
          (u b - u a) / (b - a) = (qa + qb) / 2 ∧
          ∀ y : ℝ, lemma1Quad u a b qa qb y ≤ u y := by sorry

end RobustMeanCov.TwoPoint
