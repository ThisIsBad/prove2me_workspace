import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model

namespace RetailVariety.Fashion

/-- The function `g(x) = ((p − c)λ/L) x − (pσλ^β e^{−z²/2}/(√(2π) L^β)) x^β` of the proof of
Theorem 3, p. 1506 (with `L = ∑_{j=1}^r v_j + v_0` supplied by the caller). -/
noncomputable def gFun (p c lam σ β L : ℝ) (x : ℝ) : ℝ :=
  (p - c) * lam / L * x - safetyCoeff p c lam σ β / L ^ β * x ^ β

/-- The function `g^T(x) = (λ/L)(px − cL)^+` of the proof of Theorem 3, p. 1506. -/
noncomputable def gFunT (p c lam L : ℝ) (x : ℝ) : ℝ :=
  lam / L * max (p * x - c * L) 0

/-- The `r`-dimensional vector `w′ = (w_1, …, w_{t−1}, δ w_t, 0, …, 0)` of p. 1506, 0-based:
for `j : Fin r` (with `r ≤ n`), `w′ j = w j` if `j < t`, `θ · w t` if `j = t`, and `0` if `j > t`.
Here the Lean `t` is the paper's `t − 1` and `θ` is the paper's `δ`. -/
noncomputable def wPrime {n : ℕ} (w : Fin n → ℝ) (r t : ℕ) (θ : ℝ) (hr : r ≤ n) (j : Fin r) : ℝ :=
  if j.val < t then w (Fin.castLE hr j)
  else if j.val = t then θ * w (Fin.castLE hr j)
  else 0

end RetailVariety.Fashion
