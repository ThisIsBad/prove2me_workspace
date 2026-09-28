import Mathlib

namespace CalibratedCE.Generic

/-- Player 1's conditional forecast `p_{1,t}(·) = D(x_t, ·) / Σ_y D(x_t, y)` when player 1's
recommended strategy is `a`. -/
noncomputable def condForecast₁ {m n : ℕ} (D : Fin m → Fin n → ℝ) (a : Fin m) : Fin n → ℝ :=
  fun b => D a b / ∑ c, D a c

/-- Player 2's conditional forecast `p_{2,t}(·) = D(·, y_t) / Σ_x D(x, y_t)` when player 2's
recommended strategy is `b`. -/
noncomputable def condForecast₂ {m n : ℕ} (D : Fin m → Fin n → ℝ) (b : Fin n) : Fin m → ℝ :=
  fun a => D a b / ∑ c, D c b

/-- The perturbed forecasts `p_i = (1 - 1/i) p* + (1/i) q`, `i = 1, 2, …`. -/
noncomputable def pert {n : ℕ} (pstar q : Fin n → ℝ) (i : ℕ) : Fin n → ℝ :=
  fun b => (1 - 1 / (i : ℝ)) * pstar b + (1 / (i : ℝ)) * q b

end CalibratedCE.Generic
