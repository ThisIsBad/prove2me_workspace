import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One normalized verifier row, typed for the payload-preserving affine
source.  Its payload is exactly the compact one-hot source family already
computed by the seed-carrier normalization stage. -/
noncomputable def verifierValidityRowTailPayloadRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTriplePayloadRow :=
  (verifierValidityRowSeeds W input).map fun seed =>
    { seed := validityRowAffineSeed seed.height seed.start seed.rowBase
      payload := encodeAffineExactlyOneOutputSourceInvocationFamily
        (validityRowSeedOneHotFrames W.machine.tm seed).reverse }

/-- Well-formed typed family presented to the generic affine source. -/
noncomputable def verifierValidityRowTailPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTriplePayloadFamily :=
  { rows := verifierValidityRowTailPayloadRows W input
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [verifierValidityRowTailPayloadRows, List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact affineExactlyOneOutputInvocationFamily_no_frameEnd _ symbol hsymbol }
end CLRS.Chapter34.Turing.CookLevin
