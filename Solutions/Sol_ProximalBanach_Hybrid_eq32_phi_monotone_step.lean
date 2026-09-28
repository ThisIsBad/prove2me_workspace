import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

end ProximalBanach.Hybrid

open ProximalBanach.Hybrid
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [StrictConvexSpace ℝ E] (hR : IsReflexive E)
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, phi J (x (n + 1)) (x n) + phi J (x n) (x 0) ≤ phi J (x (n + 1)) (x 0) := by
  intro n
  have hW : (J (x 0) - J (x n)) (x (n + 1) - x n) ≤ 0 := ((hrun n).2.2.1).2
  have hJn : J (x n) (x n) = ‖x n‖ ^ 2 := (hJ (x n)).1
  simp only [ContinuousLinearMap.sub_apply, map_sub] at hW
  unfold phi
  linarith
