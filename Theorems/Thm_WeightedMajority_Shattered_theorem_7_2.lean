import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Shattered_ShatteredByDomain

namespace WeightedMajority.Shattered

/-- Littlestone--Warmuth, Theorem 7.2, pp. 244--245. -/
theorem theorem_7_2 {X : Type*} {n : ℕ} (φ : Fin n → X → Bool)
    (hφ : ShatteredByDomain φ) (A : UnderstandingML.OnlineAlg X Bool)
    (hfin : ∀ i, UnderstandingML.mistakeBound A ({φ i} : Set (X → Bool)) < ⊤) :
    (∑ i : Fin n, (2 : ℝ) ^ (-((UnderstandingML.mistakeBound A
      ({φ i} : Set (X → Bool))).toNat : ℤ))) < 2 := by sorry

end WeightedMajority.Shattered

