import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Proof of Theorem 6, p. 204: if `ã ∈ 𝒜` maximizes `p(·, z)` over `𝒜` and vanishes on
`𝒥₀`, then some extreme allocation `a* ∈ ℰ` (one of the extreme allocations of which `ã`
is a convex combination) maximizes `p(·, z)` over `𝒜` and vanishes on `𝒥₀`. -/
theorem extreme_maximizer_vanishing {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (at' : Fin J → ℝ) (hat : at' ∈ allocSet N)
    (hmax : ∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N at' z)
    (hvan : ∀ j ∈ J0 N z, at' j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0 := by sorry

end MaxPressure.StrictLeontief

