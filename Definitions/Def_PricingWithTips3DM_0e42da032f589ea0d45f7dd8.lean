import Definitions.Def_PricingWithTips3DM_6060943af7a531826097deb7
import Definitions.Def_PricingWithTips3DM_551411fcc9e0942b44e6b51e
import Definitions.Def_PricingWithTips3DM_a8f5b6ef34401b5c44b30a21
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Complete quoted transition rows

The recursively generated dispatch prefix and the affine post-dispatch tail
are joined pointwise at their common transition seed.  Each resulting payload
is one quoted canonical local row without its final terminator; the marked
family's literal boundary supplies that final terminator during decoding.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete delimiter-safe transition payload for every canonical seed. -/
noncomputable def verifierTransitionCompleteQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierTransitionSeedRowSource W :=
  (verifierTransitionLocalPrefixQuotedSeedRowSource W).append
    (verifierTransitionTailQuotedSeedRowSource W)

/-- Exact semantic content of one complete quoted transition row. -/
theorem verifierTransitionCompleteQuotedSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionCompleteQuotedSeedRowSource W).row seed =
      quoteUnaryFrameStream
        (.frameEnd ::
          (encodeAffineStmtControllerScript
              (transitionDispatchScriptFromSeed W.machine.tm seed) ++
            affineStmtTransitionBoundaryCode ++
            encodeAffineTransitionTail
              (transitionScriptFromSeed W.machine.tm seed
                (seed.rowBase +
                  cfgBitCount W.machine.tm seed.height)))) := by
  simp only [verifierTransitionCompleteQuotedSeedRowSource,
    VerifierTransitionSeedRowSource.append_row]
  rw [verifierTransitionLocalPrefixQuotedSeedRowSource_row_eq
    W input seed hseed]
  simp [verifierTransitionTailQuotedSeedRowSource,
    quoteUnaryFrameStream_append, List.append_assoc]

/-- Public complete quoted-row family. -/
noncomputable def verifierTransitionCompleteQuotedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierTransitionCompleteQuotedSeedRowSource W).family input

theorem verifierTransitionCompleteQuotedFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionCompleteQuotedFamily W input).rows =
      (verifierTransitionRowSeeds W input).map fun seed =>
        quoteUnaryFrameStream
          (.frameEnd ::
            (encodeAffineStmtControllerScript
                (transitionDispatchScriptFromSeed W.machine.tm seed) ++
              affineStmtTransitionBoundaryCode ++
              encodeAffineTransitionTail
                (transitionScriptFromSeed W.machine.tm seed
                  (seed.rowBase +
                    cfgBitCount W.machine.tm seed.height)))) := by
  rw [verifierTransitionCompleteQuotedFamily,
    (verifierTransitionCompleteQuotedSeedRowSource W).rows_eq]
  apply List.map_congr_left
  intro seed hseed
  exact verifierTransitionCompleteQuotedSeedRowSource_row_eq
    W input seed hseed

/-- A single fixed polynomial-time TM2 emits the complete quoted transition
row family from the raw verifier word. -/
noncomputable def
    verifierTransitionCompleteQuotedFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionCompleteQuotedFamily W) :=
  (verifierTransitionCompleteQuotedSeedRowSource W).computableInPolyTime

end CLRS.Chapter34.Turing.CookLevin
