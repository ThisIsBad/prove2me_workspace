import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part1
import Definitions.Def_PricingWithTips3DM_f464f5b73553a5ce6a25fb85
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_existing,
    ←
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames_eq]
end CLRS.Chapter34.Turing.CookLevin
