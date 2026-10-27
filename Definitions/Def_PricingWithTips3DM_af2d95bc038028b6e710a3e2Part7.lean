import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Typed view used to feed the concrete marked-row duplicator. -/
noncomputable def verifierValidityRowPlainOperandPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      encodeUnaryFrame
          (arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase) ++
        encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFrames W.machine.tm seed)
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      rw [List.mem_append] at hsymbol
      rcases hsymbol with hfixed | hcompact
      · exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hfixed
      · exact inputCompiler_compactFamily_no_frameEnd _ symbol hcompact }

/-- The typed family encoding is exactly the concrete plain source stream. -/
theorem verifierValidityRowPlainOperandPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierValidityRowPlainOperandPayloadFamily W input) =
      verifierValidityRowPlainOperandPayloadFrames W input := by
  rw [verifierValidityRowPlainOperandPayloadFrames_eq_rows]
  unfold encodeUnaryFrameMarkedRowFamily
    verifierValidityRowPlainOperandPayloadFamily
  rw [List.flatMap_map]

/-- Both physical copies of every complete plain operand row.  They arise
from one concrete input stream, not from two independently flattened sources. -/
noncomputable def verifierValidityRowDuplicatedPlainOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameDuplicatedMarkedRowFamily
    (verifierValidityRowPlainOperandPayloadFamily W input)

/-- Exact byte layout of the duplicated complete rows. -/
theorem verifierValidityRowDuplicatedPlainOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowDuplicatedPlainOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        let row :=
          encodeUnaryFrame
              (arithmeticValidityRowFixedOperandValues W.machine.tm
                seed.height seed.start seed.rowBase) ++
            encodeAffineExactlyOneCompactFamily
              (validityRowSeedOneHotFrames W.machine.tm seed)
        row ++ [.frameEnd] ++ row ++ [.frameEnd] := by
  unfold verifierValidityRowDuplicatedPlainOperandPayloadFrames
    encodeUnaryFrameDuplicatedMarkedRowFamily
    verifierValidityRowPlainOperandPayloadFamily
  rw [List.flatMap_map]

/-- One fixed polynomial-time pipeline computes both row copies directly from
the original verifier word. -/
noncomputable def
    verifierValidityRowDuplicatedPlainOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowDuplicatedPlainOperandPayloadFrames W) := by
  let plainSource :=
    verifierValidityRowPlainOperandPayloadFrames_computableInPolyTime W
  let typedPlainSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeUnaryFrameMarkedRowFamily
        (verifierValidityRowPlainOperandPayloadFamily W) :=
    { tm := plainSource.tm
      inputAlphabet := plainSource.inputAlphabet
      outputAlphabet := plainSource.outputAlphabet
      time := plainSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowPlainOperandPayloadFamily_encoding_eq W input]
          using plainSource.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedPlainSource unaryFrameMarkedRowDuplicate_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      encodeUnaryFrameDuplicatedMarkedRowFamily
        (verifierValidityRowPlainOperandPayloadFamily W input))
  simpa [Function.comp_def] using Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin
