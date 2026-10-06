import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

namespace AlgMechDesign.Randomized

/-- Theorem 4.16: for every number `k` of tasks, the randomly biased min work mechanism is a
universally strongly truthful implementation of a `7/4`-approximation (in expected make-span)
for task scheduling with two agents. -/
theorem randomly_biased_min_work {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay ∧
      ∀ t : Fin 2 → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin 2,
        expMakespan t ≤ 7 / 4 * makespan t y := by sorry

end AlgMechDesign.Randomized

