import Definitions.Def_PricingWithTips3DM_b4c86087b487e6fd844dd77b
import Definitions.Def_PricingWithTips3DM_c2c769ccc443b1a929b3ced9
import Definitions.Def_PricingWithTips3DM_016f4b89ca40933af432d715
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General CIRCUIT-SAT to SAT: many-one reduction -/

namespace CLRS.Chapter34

/-- The direct consistency-formula construction is a genuine polynomial-time
many-one reduction on the honest raw languages. -/
theorem generalCircuitSAT_reducible_to_SAT :
    PolyTimeReducible GeneralCircuitSAT SAT := by
  refine ⟨generalCircuitToSATMap,
    ⟨Turing.GeneralCircuitToSAT.computableInPolyTime⟩, ?_⟩
  intro input
  exact (generalCircuitToSATMap_mem_SAT_iff input).symm

/-- SAT is NP-hard, obtained directly from the completed Cook--Levin target
and the verified general-circuit-to-formula machine. -/
theorem SAT_npHard : NPHard SAT :=
  NPHard.of_reducible Turing.CookLevin.generalCircuitSAT_npHard
    generalCircuitSAT_reducible_to_SAT

end CLRS.Chapter34
