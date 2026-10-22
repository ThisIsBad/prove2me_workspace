import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Proof of Lemma 3, p. 208: in a reversed Leontief network, for an extreme allocation `a`,
`j_k(a) ∈ 𝒥(k)` for every processor `k`, and `p(a, z) = ∑_k p(j_k(a), z)` for every `z`. -/
theorem pressure_split_by_processor {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) :
    (∀ k, activityOf N a k ∈ procActs N k) ∧
    ∀ z : Fin I → ℝ, pressure N a z = ∑ k, actPressure' N (activityOf N a k) z := by sorry

end MaxPressure.ReversedLeontief

