import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Delimiter-materialized unified row packets.  The compact one-hot payload
is still retained verbatim for the final row-local expansion/projection stage. -/
noncomputable def verifierValidityRowSplicedOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixSplice
    (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
    (verifierValidityRowUnifiedOperandPayloadFrames W input)

/-- Exact row-major semantics after materializing every fixed delimiter. -/
theorem verifierValidityRowSplicedOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowSplicedOperandPayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceOutputFamily
        (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
        (fun seed : ValidityRowSeed =>
          arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed))
        (verifierValidityRowSeeds W input) := by
  unfold verifierValidityRowSplicedOperandPayloadFrames
  rw [verifierValidityRowUnifiedOperandPayloadFrames_eq_spliceInput]
  apply rewriteUnaryFrameFixedPrefixSplice_family
  · intro seed
    exact arithmeticValidityRowFixedOperandValues_length W.machine.tm
      seed.height seed.start seed.rowBase
  · intro seed symbol hsymbol
    exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol

/-- Expanded row view of the spliced stream, exposing the exact halted
boundary and the unchanged compact one-hot payload. -/
theorem verifierValidityRowSplicedOperandPayloadFrames_eq_explicit
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowSplicedOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            [ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
              seed.rowBase,
              arithmeticNoneLabelWire W.machine.tm seed.rowBase ] ++
          [.frameEnd] ++
          encodeUnaryFrameWithFixedDelimiters
            (arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase)
            (arithmeticValidityTailFixedOperandDelimiters W.machine.tm) ++
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed) ++
          [.frameEnd] := by
  rw [verifierValidityRowSplicedOperandPayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [encodeUnaryFrameFixedPrefixSpliceOutputFamily,
        List.flatMap_cons]
      rw [arithmeticValidityRowFixedEncoding_eq, ih]

/-- One fixed polynomial-time pipeline computes the delimiter-materialized
unified packets directly from the original verifier word. -/
noncomputable def
    verifierValidityRowSplicedOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowSplicedOperandPayloadFrames W) := by
  let unifiedSource :=
    verifierValidityRowUnifiedOperandPayloadFrames_computableInPolyTime W
  let spliceSource := unaryFrameFixedPrefixSplice_computableInPolyTime
    (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unifiedSource spliceSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameFixedPrefixSplice
        (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
        (verifierValidityRowUnifiedOperandPayloadFrames W input))
  simpa [Function.comp_def] using Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin
