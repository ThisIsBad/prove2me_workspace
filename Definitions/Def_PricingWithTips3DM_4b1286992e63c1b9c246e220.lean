import Definitions.Def_PricingWithTips3DM_3501ec8234bc4dc2fc4f66bd
import Definitions.Def_PricingWithTips3DM_bc8afa389c894e59aa124753
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial runtime of quoted delimiter materialization
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem unaryFrameQuotedDelimiterMapSteps_le
    (input : List UnaryFrameSym) :
    unaryFrameQuotedDelimiterMapSteps input ≤ 3 * input.length + 2 := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp only [unaryFrameQuotedDelimiterMapSteps, List.length_cons] <;>
        omega

/-- The prepend-only implementation runs in a uniform linear bound. -/
noncomputable def unaryFrameQuotedDelimiterMapRev_computableInPolyTime
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (rewriteUnaryFrameQuotedDelimiters delimiters hnonempty input
          ).reverse) where
  tm := compile (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 2
  outputsFun := fun input => by
    have builderRun := unaryFrameQuotedDelimiterMapRev_run delimiters
      hnonempty input
    have compiledRun := compile_evalsToInTime
      (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile
          (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty)).step
        (_root_.Turing.initList
          (compile
            (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty))
          input)
        (some (_root_.Turing.haltList
          (compile
            (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty))
          (rewriteUnaryFrameQuotedDelimiters delimiters hnonempty input
            ).reverse))
        (unaryFrameQuotedDelimiterMapSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameQuotedDelimiterMapSteps input ≤
        (3 * Polynomial.X + 2).eval input.length := by
      simpa using unaryFrameQuotedDelimiterMapSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile
          (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty)).step
        (_root_.Turing.initList
          (compile
            (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty))
          input)
        (some (_root_.Turing.haltList
          (compile
            (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty))
          (rewriteUnaryFrameQuotedDelimiters delimiters hnonempty input
            ).reverse))
        ((3 * Polynomial.X + 2).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order combined delimiter materialization and quotation. -/
noncomputable def unaryFrameQuotedDelimiterMap_computableInPolyTime
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameQuotedDelimiters delimiters hnonempty) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameQuotedDelimiterMapRev_computableInPolyTime delimiters
        hnonempty)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
