import Mathlib

namespace RobustMeanCov.TwoPoint

/-- The coefficient `A = (q_b - q_a) / (2 (b - a))` of Lemma 1(c) (Popescu 2007, p. 102). -/
noncomputable def lemma1A (a b qa qb : ℝ) : ℝ :=
  (qb - qa) / (2 * (b - a))

/-- The coefficient `B = (b q_a - a q_b) / (b - a)` of Lemma 1(c). -/
noncomputable def lemma1B (a b qa qb : ℝ) : ℝ :=
  (b * qa - a * qb) / (b - a)

/-- The coefficient `C = (b u(a) - a u(b)) / (b - a) - a b (q_a - q_b) / (2 (b - a))`
of Lemma 1(c). -/
noncomputable def lemma1C (u : ℝ → ℝ) (a b qa qb : ℝ) : ℝ :=
  (b * u a - a * u b) / (b - a) - a * b * ((qa - qb) / (2 * (b - a)))

/-- The quadratic `q(y) = A y² + B y + C` of Lemma 1(c). -/
noncomputable def lemma1Quad (u : ℝ → ℝ) (a b qa qb : ℝ) (y : ℝ) : ℝ :=
  lemma1A a b qa qb * y ^ 2 + lemma1B a b qa qb * y + lemma1C u a b qa qb

end RobustMeanCov.TwoPoint
