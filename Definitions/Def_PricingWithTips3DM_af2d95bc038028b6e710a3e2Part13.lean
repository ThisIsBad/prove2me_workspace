import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part12
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Expand every compact tail behind its canonical row prefixes -/

/-- Typed view of the compact row stream consumed by the continuous
prefix-preserving validity-tail source. -/
noncomputable def verifierValidityRowPrefixedTailSourceFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AffineValidityTailPrefixedSourceFamily
      (arithmeticRuntimeStackSourceBlankSteps W.machine.tm) :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      { first := .tick :: encodeAffineExactlyOneFamily
          (validityRowSeedOneHotFrames W.machine.tm seed)
        second := encodeUnaryFrame
          [ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
            seed.rowBase,
            arithmeticNoneLabelWire W.machine.tm seed.rowBase ]
        tail := arithmeticValidityTailSourceFrame W.machine.tm
          seed.height seed.start seed.rowBase }
    first_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      simp only [List.mem_cons] at hsymbol
      rcases hsymbol with rfl | hfamily
      · simp
      · exact inputCompiler_exactlyOneFamily_no_frameEnd _ symbol hfamily
    second_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hsymbol
    stack_lengths := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact arithmeticRuntimeStackSourceSeeds_length
        W.machine.tm seed.height seed.start seed.rowBase }

/-- Retyping the compact raw-input result loses no bytes: it is exactly the
generic prefixed-tail family input. -/
theorem verifierValidityRowPrefixedTailSourceFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineValidityTailPrefixedSourceInput
        (verifierValidityRowPrefixedTailSourceFamily W input) =
      verifierValidityRowCompactSourceFrames W input := by
  rw [verifierValidityRowCompactSourceFrames_eq_invocations]
  unfold encodeAffineValidityTailPrefixedSourceInput
    verifierValidityRowPrefixedTailSourceFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]
end CLRS.Chapter34.Turing.CookLevin
