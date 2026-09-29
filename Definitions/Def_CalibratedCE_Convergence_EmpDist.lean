import Mathlib

namespace CalibratedCE.Convergence

/-- `D_t(x, y)`: the fraction of the first `t` rounds (rounds `0, …, t-1`) in which player 1
played `a` and player 2 played `b`. At `t = 0` it is `0` (division by zero). -/
noncomputable def empDist {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ) (a : Fin m)
    (b : Fin n) : ℝ :=
  (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) / (t : ℝ)

end CalibratedCE.Convergence
