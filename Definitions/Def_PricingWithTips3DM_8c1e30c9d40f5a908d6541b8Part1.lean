import Definitions.Def_PricingWithTips3DM_ed1da04e55c84fc3dcce3010
import Definitions.Def_PricingWithTips3DM_5fa2c8ddc93042763c0cb53c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_existing,
    ←
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames_eq]
end CLRS.Chapter34.Turing.CookLevin
