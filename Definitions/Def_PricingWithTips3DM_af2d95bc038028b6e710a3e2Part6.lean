import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Honest duplication of the complete plain row packet -/

/-- Before assigning the canonical mixed delimiter table, every fixed field
can be terminated by an ordinary separator.  This removes all internal
`frameEnd` symbols, leaving the one final row marker available to the generic
marked-row duplicator. -/
noncomputable def arithmeticValidityRowPlainOperandDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  List.replicate (arithmeticValidityRowFixedOperandForms tm).length .separator

@[simp] theorem arithmeticValidityRowPlainOperandDelimiters_length
    (tm : _root_.Turing.FinTM2) :
    (arithmeticValidityRowPlainOperandDelimiters tm).length =
      (arithmeticValidityRowFixedOperandForms tm).length := by
  simp [arithmeticValidityRowPlainOperandDelimiters]

theorem arithmeticValidityRowPlainOperandDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (arithmeticValidityRowPlainOperandDelimiters tm).length := by
  simp [arithmeticValidityRowPlainOperandDelimiters,
    arithmeticValidityRowFixedOperandForms]

theorem inputCompiler_encodeFixedPlain_eq_frame
    (values : List Nat) :
    encodeUnaryFrameWithFixedDelimiters values
        (List.replicate values.length UnaryFrameSym.separator) =
      encodeUnaryFrame values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [show (value :: values).length = values.length + 1 by simp,
        List.replicate_succ]
      simp [encodeUnaryFrameWithFixedDelimiters, encodeUnaryFrame,
        encodeUnaryFrameBlock, ih, List.append_assoc]

/-- Plain fixed fields followed by the untouched compact one-hot payload and
one outer row marker. -/
noncomputable def verifierValidityRowPlainOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixSplice
    (arithmeticValidityRowPlainOperandDelimiters W.machine.tm)
    (verifierValidityRowUnifiedOperandPayloadFrames W input)

/-- The plain splice has no reserved row marker before the compact payload. -/
theorem verifierValidityRowPlainOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowPlainOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
          (arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase) ++
        encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFrames W.machine.tm seed) ++
        [.frameEnd] := by
  unfold verifierValidityRowPlainOperandPayloadFrames
  rw [verifierValidityRowUnifiedOperandPayloadFrames_eq_spliceInput]
  rw [rewriteUnaryFrameFixedPrefixSplice_family]
  · generalize verifierValidityRowSeeds W input = seeds
    induction seeds with
    | nil => rfl
    | cons seed rest ih =>
        simp only [encodeUnaryFrameFixedPrefixSpliceOutputFamily,
          List.flatMap_cons]
        have hforms :
            (arithmeticValidityRowFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase).length =
            (arithmeticValidityRowFixedOperandForms W.machine.tm).length := by
          rw [arithmeticValidityRowFixedOperandValues_length,
            arithmeticValidityRowFixedOperandDelimiters_length]
        have hhead :
            encodeUnaryFrameWithFixedDelimiters
                (arithmeticValidityRowFixedOperandValues W.machine.tm
                  seed.height seed.start seed.rowBase)
                (arithmeticValidityRowPlainOperandDelimiters W.machine.tm) =
              encodeUnaryFrame
                (arithmeticValidityRowFixedOperandValues W.machine.tm
                  seed.height seed.start seed.rowBase) := by
          unfold arithmeticValidityRowPlainOperandDelimiters
          rw [← hforms]
          exact inputCompiler_encodeFixedPlain_eq_frame _
        rw [hhead, ih]
  · intro seed
    rw [arithmeticValidityRowFixedOperandValues_length,
      arithmeticValidityRowFixedOperandDelimiters_length]
    exact (arithmeticValidityRowPlainOperandDelimiters_length _).symm
  · intro seed symbol hsymbol
    exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol

/-- The plain stream remains a direct polynomial-time output of the original
verifier word. -/
noncomputable def
    verifierValidityRowPlainOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowPlainOperandPayloadFrames W) := by
  let unifiedSource :=
    verifierValidityRowUnifiedOperandPayloadFrames_computableInPolyTime W
  let plainSplice := unaryFrameFixedPrefixSplice_computableInPolyTime
    (arithmeticValidityRowPlainOperandDelimiters W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unifiedSource plainSplice
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameFixedPrefixSplice
        (arithmeticValidityRowPlainOperandDelimiters W.machine.tm)
        (verifierValidityRowUnifiedOperandPayloadFrames W input))
  simpa [Function.comp_def] using Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin
