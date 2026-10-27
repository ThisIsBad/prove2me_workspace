import Definitions.Def_PricingWithTips3DM_dc64d7b212917919c814212b
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial runtime of marked-row unary-frame unquoting
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The concrete marked-row decoder, before forward-order restoration. -/
noncomputable def unaryFrameMarkedRowsUnquoteRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (unquoteUnaryFrameMarkedRows input).reverse) where
  tm := compile unaryFrameMarkedRowsUnquoteRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun input => by
    have builderRun := unaryFrameMarkedRowsUnquoteRev_run input
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedRowsUnquoteRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowsUnquoteRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowsUnquoteRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowsUnquoteRevProgram)
          (unquoteUnaryFrameMarkedRows input).reverse))
        (unaryFrameMarkedRowsUnquoteSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedRowsUnquoteSteps input ≤
        (3 * Polynomial.X + 3).eval input.length := by
      simpa using unaryFrameMarkedRowsUnquoteSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowsUnquoteRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowsUnquoteRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowsUnquoteRevProgram)
          (unquoteUnaryFrameMarkedRows input).reverse))
        ((3 * Polynomial.X + 3).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order marked-row decoding is polynomial-time computable. -/
noncomputable def unaryFrameMarkedRowsUnquote_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      unquoteUnaryFrameMarkedRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedRowsUnquoteRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        simpa [Function.comp_def] using run }

end CLRS.Chapter34.Turing.PolyBuilder
