import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology

namespace KendallBD.Cumul

theorem cumulative_law (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w) ∧
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      Summable (fun M : ℕ => Q lam0 mu0 M * w ^ M) ∧
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (∑' M : ℕ, Q lam0 mu0 M * w ^ M))) ∧
    ((∀ M : ℕ, 0 ≤ Q lam0 mu0 M) ∧ HasSum (Q lam0 mu0) 1) := by sorry

end KendallBD.Cumul

