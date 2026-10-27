import Definitions.Def_PricingWithTips3DM_e54fd9f21278f9dc24c110df
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial runtime of unary-frame unquoting
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The concrete total decoder, before forward-order restoration. -/
noncomputable def unaryFrameUnquoteRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (unquoteUnaryFrameStream input).reverse) where
  tm := compile unaryFrameUnquoteRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun input => by
    have builderRun := unaryFrameUnquoteRev_run input
    have compiledRun := compile_evalsToInTime
      unaryFrameUnquoteRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameUnquoteRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameUnquoteRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameUnquoteRevProgram)
          (unquoteUnaryFrameStream input).reverse))
        (unaryFrameUnquoteSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameUnquoteSteps input ≤
        (3 * Polynomial.X + 3).eval input.length := by
      simpa using unaryFrameUnquoteSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameUnquoteRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameUnquoteRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameUnquoteRevProgram)
          (unquoteUnaryFrameStream input).reverse))
        ((3 * Polynomial.X + 3).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Total forward-order unary-frame decoding is polynomial-time computable. -/
noncomputable def unaryFrameUnquote_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      unquoteUnaryFrameStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameUnquoteRev_computableInPolyTime
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
