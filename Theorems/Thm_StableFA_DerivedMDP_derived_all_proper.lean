import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

namespace StableFA.DerivedMDP

theorem derived_all_proper {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    (∃ m : ℕ, 0 < m ∧ ∀ π : ℕ → Fin n → C, BertsekasSSPAdmissible (derivedModel M A 1) π →
        ∀ i, BertsekasSSPSurvival (derivedModel M A 1) π m i < 1) ∧
      ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper (derivedModel M A 1) μ := by sorry

end StableFA.DerivedMDP

