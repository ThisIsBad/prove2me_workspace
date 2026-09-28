import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronNumUpdates
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronUpdates

namespace FoundationsML.OnlineLearning

/-- Theorem 8.11 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 196, PDF p. 213). Let `I` be the set of update rounds of the Perceptron
algorithm processing `x_1,…,x_T` with `‖x_t‖ ≤ r`. Then `M = |I|` satisfies
`M ≤ inf_{ρ>0, ‖v‖₂≤1} [(r/ρ + sqrt(r²/ρ² + 4‖l_ρ‖₁))/2]²`, where
`l_ρ = (l_t)_{t∈I}` with `l_t = max{0, 1 − y_t(v·x_t)/ρ}`. -/
theorem perceptron_hinge_mistake_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (T : ℕ) (r : ℝ) (hr : 0 < r) (hxr : ∀ t < T, ‖x t‖ ≤ r) :
    (PerceptronNumUpdates x y T : ℝ) ≤
      ⨅ ρ ∈ Set.Ioi (0 : ℝ), ⨅ v ∈ Metric.closedBall (0 : V) 1,
        ((r / ρ + Real.sqrt (r ^ 2 / ρ ^ 2 +
            4 * ∑ t ∈ PerceptronUpdates x y T,
              max 0 (1 - y t * (inner (𝕜 := ℝ) v (x t) : ℝ) / ρ))) /
          2) ^ 2 := by sorry

end FoundationsML.OnlineLearning
