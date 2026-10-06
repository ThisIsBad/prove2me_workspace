import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

namespace AlgMechDesign.Randomized

/-- Lemma 4.18: for every number `k` of tasks, every positive type vector `t` of the two agents
and every allocation `y`, the expected make-span of the randomly biased min work mechanism is at
most `7/4` times the make-span of `y`. -/
theorem rbmw_approx {k : ℕ} (t : Fin 2 → Fin k → ℝ) (ht : IsType t) (y : Fin k → Fin 2) :
    expMakespan t ≤ 7 / 4 * makespan t y := by sorry

end AlgMechDesign.Randomized

