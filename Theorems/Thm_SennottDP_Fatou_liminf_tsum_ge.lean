import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.1.7, p. 273, (A.3). `S` is countable and `u(j, N) ∈ [0, ∞]`:
`liminf_N ∑_{j ∈ S} u(j, N) ≥ ∑_{j ∈ S} liminf_N u(j, N)`. -/
theorem liminf_tsum_ge {S : Type*} [Countable S] (u : S → ℕ → ℝ≥0∞) :
    ∑' j, liminf (fun N => u j N) atTop ≤ liminf (fun N => ∑' j, u j N) atTop := by sorry

end SennottDP.Fatou
