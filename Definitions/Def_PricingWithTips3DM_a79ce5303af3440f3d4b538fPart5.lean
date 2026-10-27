import Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538fPart4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw-input descriptor stream for all equality segments of all transition
rows. -/
noncomputable def verifierTransitionEqProgressionDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionEqProgressionDescriptorForms W.machine.tm) input

/-- Exact byte semantics of the raw-input descriptor source. -/
theorem verifierTransitionEqProgressionDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqProgressionDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqProgressions W.machine.tm)) := by
  unfold verifierTransitionEqProgressionDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionEqProgressionDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionEqProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions segmentIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, segmentIh]

/-- One fixed polynomial-time TM2 emits all equality progression descriptors
directly from the raw verifier input. -/
noncomputable def
    verifierTransitionEqProgressionDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqProgressionDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionEqProgressionDescriptorForms W.machine.tm)
end CLRS.Chapter34.Turing.CookLevin
