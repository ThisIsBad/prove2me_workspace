import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace CompetitivePaging.LowerBound

theorem no_competitive_below_harmonic (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (M : Type)
    [MetricSpace M] (e : Fin n ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.RandomizedAlgorithm k M) (C₀ : KServer.Config k M) (c : ℝ)
    (hc : c < (harmonic k : ℝ)) :
    ¬ A.IsCompetitiveFrom C₀ c := by sorry

end CompetitivePaging.LowerBound

