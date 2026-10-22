import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Proof of Theorem 6, p. 204 ("It is sufficient to show"): for `z ∈ ℝ^I_+`, if some
extreme allocation maximizes `p(·, z)` over `ℰ` and vanishes on `𝒥₀`, then some extreme
allocation maximizes `p(·, z)` over `ℰ` and every constituent buffer of it has a positive
level, which is the conclusion of Assumption 1 at `z`. -/
theorem reduction {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (h : ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i := by sorry

end MaxPressure.StrictLeontief

