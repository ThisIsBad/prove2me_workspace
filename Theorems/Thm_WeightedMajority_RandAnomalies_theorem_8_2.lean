import Definitions.Def_WeightedMajority_RandAnomalies_OptRand

open scoped ENNReal

namespace WeightedMajority.RandAnomalies

/-- **Theorem 8.2** (Littlestone–Warmuth 1994, p. 252). For all target classes `F` and all
`η ≥ 0`, if `|F| > 1` then `opt_RAND(F, η) ≥ ½ opt(F, 0) + η`. -/
theorem theorem_8_2 {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    ((WeightedMajority.Anomalies.opt F 0 : ℕ∞) : ℝ≥0∞) / 2 + η ≤ optRand F η := by sorry

end WeightedMajority.RandAnomalies

