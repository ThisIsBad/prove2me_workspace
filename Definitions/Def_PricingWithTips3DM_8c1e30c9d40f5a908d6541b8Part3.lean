import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part2
import Definitions.Def_PricingWithTips3DM_7567c18233bee2ade1bb1d40
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_existing,
    ← verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames_eq]
end CLRS.Chapter34.Turing.CookLevin
