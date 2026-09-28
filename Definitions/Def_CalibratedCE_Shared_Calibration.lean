import Mathlib

open Filter Topology

namespace CalibratedCE.Shared

/-- `N(p, t)`: the number of rounds among the first `t` (rounds `0, …, t-1`) in which the
forecast sequence `f` issued the forecast vector `p`. -/
noncomputable def N {k : ℕ} (f : ℕ → Fin k → ℝ) (p : Fin k → ℝ) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s => f s = p)).card

/-- `ρ(p, j, t)`: among the first `t` rounds in which `f` forecast `p`, the fraction in which
the opponent played `j`; it is `0` when `N(p, t) = 0`. -/
noncomputable def rho {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (p : Fin k → ℝ) (j : Fin k)
    (t : ℕ) : ℝ :=
  if N f p t = 0 then 0
  else (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) / (N f p t : ℝ)

/-- The calibration score `∑_p |ρ(p, j, t) - p_j| N(p, t) / t`, the sum running over the
forecasts issued in the first `t` rounds (every other `p` has `N(p, t) = 0`). -/
noncomputable def calibScore {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (j : Fin k)
    (t : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range t).image f, |rho f z p j t - p j| * (N f p t : ℝ) / (t : ℝ)

/-- The forecast sequence `f` is calibrated with respect to the opponent's plays `z`: for every
opponent strategy `j` the calibration score tends to `0`. -/
def Calibrated {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) : Prop :=
  ∀ j : Fin k, Tendsto (fun t : ℕ => calibScore f z j t) atTop (𝓝 0)

end CalibratedCE.Shared
