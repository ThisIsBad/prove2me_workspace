import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb

namespace CompetitivePaging.LowerBound

theorem expCost_append_ge_uncoveredProb {k : ℕ} (M : Type) [MetricSpace M]
    (hd : ∀ x y : M, x ≠ y → dist x y = 1) (A : KServer.RandomizedAlgorithm k M)
    (σ : List M) (i : M)
    (hmeas : @MeasurableSet A.ι A.ms {ω | i ∉ Set.range ((A.alg ω).conf σ)}) :
    A.expCost σ + ENNReal.ofReal (uncoveredProb A σ i) ≤ A.expCost (σ ++ [i]) := by sorry

end CompetitivePaging.LowerBound
