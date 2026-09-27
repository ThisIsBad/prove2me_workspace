import Definitions.Def_fep_finite_laws
import Definitions.Def_fep_finite_information
import Definitions.Def_fep_generative_model
import Definitions.Def_fep2_expected_free_energy

namespace FreeEnergyPrinciple

theorem expectedFreeEnergy_eq_risk_add_ambiguity
    {Policy State Outcome : Type*} [Fintype Policy] [Fintype State]
    [Fintype Outcome]
    (model : GenerativeModel Policy State Outcome) (policy : Policy)
    (support : FullSupport model) :
    expectedFreeEnergy model policy =
      risk model policy + ambiguity model policy := by sorry

end FreeEnergyPrinciple
