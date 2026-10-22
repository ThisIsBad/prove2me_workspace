import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

namespace StableFA.DerivedMDP

theorem corollary_4_1 {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    StableFA.Discounted.Compatible A.apply (BertsekasSSPBellmanOp M) ∧
      StableFA.Discounted.Compatible (BertsekasSSPBellmanOp M) A.apply := by sorry

end StableFA.DerivedMDP

