import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The normalized seed-first byte stream is definitionally the concrete
encoding of the typed payload family. -/
theorem verifierValidityRowTailPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowTailPayloadFamily W input) =
      verifierValidityRowSeedFirstOutputInvocationFrames W input := by
  rw [verifierValidityRowSeedFirstOutputInvocationFrames_eq_rows]
  unfold encodeAffineUnaryTriplePayloadFamily
  change encodeAffineUnaryTriplePayloadRowFamily
      (verifierValidityRowTailPayloadRows W input) = _
  unfold verifierValidityRowTailPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, encodeAffineUnaryTriplePayloadRowFamily,
        List.flatMap_cons]
      rw [ih]
      simp [encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed, validityRowAffineSeed,
        List.append_assoc]
end CLRS.Chapter34.Turing.CookLevin
