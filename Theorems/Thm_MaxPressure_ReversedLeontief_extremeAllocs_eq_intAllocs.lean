import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Lemma 1, p. 207: for a reversed Leontief network, every extreme allocation is an integer
allocation; i.e., `ℰ = 𝒩`. -/
theorem extremeAllocs_eq_intAllocs {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) :
    extremeAllocs N = intAllocs N := by sorry

end MaxPressure.ReversedLeontief

