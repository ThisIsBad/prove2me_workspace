import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The raw verifier word polynomially computes every row's fixed affine
operands while carrying the variable one-hot source invocations unchanged. -/
noncomputable def
    verifierValidityRowTailAffinePayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailAffinePayloadFrames W) := by
  let normalizedSource :=
    verifierValidityRowSeedFirstOutputInvocationFrames_computableInPolyTime W
  let typedNormalizedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowTailPayloadFamily W) :=
    { tm := normalizedSource.tm
      inputAlphabet := normalizedSource.inputAlphabet
      outputAlphabet := normalizedSource.outputAlphabet
      time := normalizedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailPayloadFamily_encoding_eq W input] using
          normalizedSource.outputsFun input }
  let affineSource := affineUnaryTriplePayloadFamily_computableInPolyTime
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedNormalizedSource affineSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      affineUnaryTriplePayloadRowOutputFamily
        (arithmeticValidityTailFixedOperandForms W.machine.tm)
        (verifierValidityRowTailPayloadRows W input))
  simpa [Function.comp_def, verifierValidityRowTailPayloadFamily] using
    Classical.choice composed

/-- The affine stage is exactly the generic fixed-prefix splice input: one
ordinary fixed table, an internal boundary, the protected one-hot payload,
and the outer row boundary. -/
theorem verifierValidityRowTailAffinePayloadFrames_eq_spliceInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailAffinePayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceInputFamily
        (fun seed : ValidityRowSeed =>
          arithmeticValidityTailFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneOutputSourceInvocationFamily
            (validityRowSeedOneHotFrames W.machine.tm seed).reverse)
        (verifierValidityRowSeeds W input) := by
  rw [verifierValidityRowTailAffinePayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons,
        encodeUnaryFrameFixedPrefixSpliceInputFamily]
      rw [ih]
end CLRS.Chapter34.Turing.CookLevin
