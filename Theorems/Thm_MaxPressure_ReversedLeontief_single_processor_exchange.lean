import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Proof of Lemma 3, p. 208: in a reversed Leontief network, for an extreme allocation `a`,
a processor `k` and `o ∈ 𝒥(k)`, the allocation `ã = a − e_{j_k(a)} + e_o` (with `e_0 = 0`
for the idle Activity 0) is extreme, and `p(ã, z) = p(a, z) − p(j_k(a), z) + p(o, z)`. -/
theorem single_processor_exchange {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) (k : Fin K)
    (o : Option (Fin J)) (ho : o ∈ procActs N k) :
    a - unitVec (activityOf N a k) + unitVec o ∈ extremeAllocs N ∧
    ∀ z : Fin I → ℝ, pressure N (a - unitVec (activityOf N a k) + unitVec o) z =
      pressure N a z - actPressure' N (activityOf N a k) z + actPressure' N o z := by sorry

end MaxPressure.ReversedLeontief

