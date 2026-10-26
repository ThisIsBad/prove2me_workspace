import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Corollary 17.3 (p. 266). If the primal feasible set has nonempty interior and is bounded (or
the dual feasible set has nonempty interior and is bounded), then for each `μ > 0` the system
(17.6) has a unique solution `(x_μ, w_μ, y_μ, z_μ)` with `x_μ, w_μ, y_μ, z_μ > 0`. -/
theorem central_path_exists_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (h : (PrimalStrictlyFeasible A b ∧ Bornology.IsBounded (primalFeasibleSet A b)) ∨
      (DualStrictlyFeasible A c ∧ Bornology.IsBounded (dualFeasibleSet A c))) :
    ∀ μ : ℝ, 0 < μ →
      ∃! p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) × (Fin n → ℝ),
        IsCentralPathPoint A b c μ p.1 p.2.1 p.2.2.1 p.2.2.2 := by sorry

end VanderbeiLP.CentralPath

