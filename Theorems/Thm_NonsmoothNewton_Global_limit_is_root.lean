import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, middle): along a run of (3.2) that stays in the
closed ball `S` and converges to `xstar`, the generalized Jacobians `V k` are uniformly bounded,
`xstar ∈ S`, and `F xstar = 0`. -/
theorem limit_is_root {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by sorry

end NonsmoothNewton.Global
