import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace CompetitivePaging.LowerBound

theorem no_competitive_below_harmonic_n_sub_one (n : ℕ) (hn : 2 ≤ n) (M : Type) [MetricSpace M]
    (e : Fin n ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.RandomizedAlgorithm (n - 1) M) (C₀ : KServer.Config (n - 1) M) (c : ℝ)
    (hc : c < (harmonic (n - 1) : ℝ)) :
    ¬ A.IsCompetitiveFrom C₀ c := by sorry

end CompetitivePaging.LowerBound

