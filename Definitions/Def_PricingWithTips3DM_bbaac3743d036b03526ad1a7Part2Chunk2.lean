import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Marked fixed-operand byte stream emitted for every verifier row.  The
cycle resets after the four final prefix fields because its period is exactly
one row's fixed affine table. -/
noncomputable def verifierValidityRowTailMarkedFixedOperandFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
    (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
    (encodeUnaryFrame (verifierValidityRowTailFixedOperandValues W input))

/-- Byte-level semantics of the marked fixed stream: the declared row table
is applied to the affine values, so each stack's internal zero field and
outer height field are terminated by `frameEnd`, while all other fixed fields
retain `separator`. -/
theorem verifierValidityRowTailMarkedFixedOperandFrames_eq_cycle
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailMarkedFixedOperandFrames W input =
      encodeUnaryFrameWithDelimiterCycle
        (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
        (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
        (verifierValidityRowTailFixedOperandValues W input) := by
  exact rewriteUnaryFrameDelimiters_encodeUnaryFrame
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
    (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
    (verifierValidityRowTailFixedOperandValues W input)

/-- The raw verifier word computes the fixed validity-tail operand stream
with every stack-family boundary already materialized as `frameEnd`. -/
noncomputable def
    verifierValidityRowTailMarkedFixedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailMarkedFixedOperandFrames W) := by
  let valueSource :=
    verifierValidityRowTailFixedOperandFrames_computableInPolyTime W
  let delimiterSource :=
    unaryFrameDelimiterMap_computableInPolyTime
      (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
      (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      valueSource delimiterSource
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierValidityRowTailMarkedFixedOperandFrames] using run }

/-! ## Payload-preserving row source -/
end CLRS.Chapter34.Turing.CookLevin
