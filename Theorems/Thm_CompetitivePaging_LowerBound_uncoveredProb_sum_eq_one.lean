import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb

namespace CompetitivePaging.LowerBound

theorem uncoveredProb_sum_eq_one (n : ℕ) (hn : 2 ≤ n) (M : Type) [MetricSpace M] [Fintype M]
    (hM : Fintype.card M = n) (A : KServer.RandomizedAlgorithm (n - 1) M) (σ : List M)
    (hinj : ∀ ω, Function.Injective ((A.alg ω).conf σ))
    (hmeas : ∀ i : M, @MeasurableSet A.ι A.ms {ω | i ∉ Set.range ((A.alg ω).conf σ)}) :
    ∑ i, uncoveredProb A σ i = 1 := by sorry

end CompetitivePaging.LowerBound
