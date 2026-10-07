import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt

namespace WeightedMajority.Anomalies

/-- Littlestone and Warmuth's Theorem 8.1 (p. 250): for every class `F` of `{0,1}`-valued
functions with `|F| > 1` and every `η ≥ 0`, `opt(F, η) ≥ opt(F, 0) + 2η`. -/
theorem theorem_8_1 {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    opt F 0 + 2 * (η : ℕ∞) ≤ opt F η := by sorry

end WeightedMajority.Anomalies

