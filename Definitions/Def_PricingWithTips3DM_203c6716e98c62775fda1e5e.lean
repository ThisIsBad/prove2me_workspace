import Definitions.Def_PricingWithTips3DM_b273d9a0a98624995a8d7aae
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: forward polynomial-time interface -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Composing the direct emitter with the verified generic reversal machine
returns the forward exact formula stream. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeGuardedCircuit id
      guardedCircuitFormulaList := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reverseComputableInPolyTime
      (PolyBuilder.reverse_computableInPolyTime (Γ := FormulaSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
