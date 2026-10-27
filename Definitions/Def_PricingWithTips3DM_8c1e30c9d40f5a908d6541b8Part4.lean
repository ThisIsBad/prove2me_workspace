import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part3
import Definitions.Def_PricingWithTips3DM_a1c02e7eaac6891e9c299d1d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_existing,
    ← verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames_eq]
end CLRS.Chapter34.Turing.CookLevin
