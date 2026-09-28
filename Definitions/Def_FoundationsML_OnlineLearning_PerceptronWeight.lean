import Mathlib

namespace FoundationsML.OnlineLearning

/-- The Perceptron algorithm's weight vector `w_t` at the start of round `t` (`t = 0` is the
initial `w_1 = 0` of Figure 8.6 line 1; `t + 1` is `w_{t+2}`, obtained from `w_{t+1}` by the
update of Figure 8.6 lines 6-8 using round `t`'s point `x t` and label `y t`) (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Figure
8.6, p. 190, PDF p. 207, in the equivalent sign-agreement form of Eq. (8.23), PDF p. 209). -/
noncomputable def PerceptronWeight {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) : ℕ → V
  | 0 => 0
  | t + 1 =>
      if y t * (inner (𝕜 := ℝ) (PerceptronWeight x y t) (x t) : ℝ) ≤ 0
      then PerceptronWeight x y t + y t • x t
      else PerceptronWeight x y t

end FoundationsML.OnlineLearning
