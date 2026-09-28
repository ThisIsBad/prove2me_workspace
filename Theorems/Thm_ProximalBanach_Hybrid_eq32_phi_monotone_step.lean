import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Display (3.2) (proof of Theorem 8, p. 943): under the hypotheses of Proposition 7, every
run of (3.1) satisfies `φ(x_{n+1}, x_n) + φ(x_n, x_0) ≤ φ(x_{n+1}, x_0)` for all `n`. -/
theorem eq32_phi_monotone_step [StrictConvexSpace ℝ E] (hR : IsReflexive E)
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, phi J (x (n + 1)) (x n) + phi J (x n) (x 0) ≤ phi J (x (n + 1)) (x 0) := by sorry

end ProximalBanach.Hybrid
