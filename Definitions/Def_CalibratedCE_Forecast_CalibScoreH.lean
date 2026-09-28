import Mathlib

namespace CalibratedCE.Forecast

open Classical

/-- `N(p, t)` read off a finite history `h` of (forecast, opponent's play) pairs, oldest first:
the number of rounds of `h` in which the forecast was exactly the vector `p`. -/
noncomputable def NH {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) : ℕ :=
  (h.filter (fun e => e.1 = p)).length

/-- `ρ(p, j, t)` read off a history `h`: among the rounds of `h` with forecast `p`, the fraction
in which the opponent played `j`; it is `0` when `p` was never forecast. -/
noncomputable def rhoH {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) (j : Fin n) :
    ℝ :=
  if NH h p = 0 then 0
  else ((h.filter (fun e => e.1 = p ∧ e.2 = j)).length : ℝ) / (NH h p : ℝ)

/-- The calibration score `C_t` of Eq. (1), read off a history `h` of length `t`:
`∑_p ∑_j |ρ(p, j, t) - p_j| N(p, t) / t`, the sum over `p` running over the forecasts that occur
in `h` (every other `p` has `N(p, t) = 0`). -/
noncomputable def calibScoreH {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, ∑ j : Fin n,
    |rhoH h p j - p j| * (NH h p : ℝ) / (h.length : ℝ)

/-- The L-1 calibration score for the single opponent strategy `j`:
`∑_p |ρ(p, j, t) - p_j| N(p, t) / t`. -/
noncomputable def calibScoreHj {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, |rhoH h p j - p j| * (NH h p : ℝ) / (h.length : ℝ)

/-- The L-2 calibration score `C_2(t)` for the opponent strategy `j` (p. 54):
`∑_p (ρ(p, j, t) - p_j)^2 N(p, t) / t`. -/
noncomputable def calibScore2Hj {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, (rhoH h p j - p j) ^ 2 * (NH h p : ℝ) / (h.length : ℝ)

end CalibratedCE.Forecast
