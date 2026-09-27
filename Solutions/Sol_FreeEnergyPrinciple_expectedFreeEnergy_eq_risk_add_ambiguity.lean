import Mathlib
import Definitions.Def_fep_finite_laws
import Definitions.Def_fep_finite_information
import Definitions.Def_fep_generative_model
import Definitions.Def_fep2_expected_free_energy



namespace FreeEnergyPrinciple

theorem fep_main {Policy State Outcome : Type*} [Fintype Policy] [Fintype State]
    [Fintype Outcome]
    (model : GenerativeModel Policy State Outcome) (policy : Policy)
    (support : FullSupport model) :
    expectedFreeEnergy model policy =
      risk model policy + ambiguity model policy := by
  rw [expectedFreeEnergy, risk_eq_crossEntropy_sub_entropy model policy support,
    epistemicValue_eq_entropy_sub_ambiguity model policy support]
  ring

end FreeEnergyPrinciple

open FreeEnergyPrinciple

theorem solution
    {Policy State Outcome : Type*} [Fintype Policy] [Fintype State]
    [Fintype Outcome]
    (model : GenerativeModel Policy State Outcome) (policy : Policy)
    (support : FullSupport model) :
    expectedFreeEnergy model policy =
      risk model policy + ambiguity model policy := by
  exact fep_main model policy support
