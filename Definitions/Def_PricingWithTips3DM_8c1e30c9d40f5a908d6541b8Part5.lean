import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Machine-level evidence for the four independently executed label-major
channels.  A consumer must still provide a physical same-input fan-out and
row zipper before treating these witnesses as one packet compiler. -/
structure TransitionDispatchMuxInvocationLabelMajorChannelCompilers
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) where
  selector : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames W)
  coordinates : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames W)
  whenTrue : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W)
  whenFalse : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W)

/-- The four concrete label-major pipelines satisfy the common compiler
interface. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorChannelCompilers
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TransitionDispatchMuxInvocationLabelMajorChannelCompilers W :=
  { selector :=
      verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_computableInPolyTime
        W
    coordinates :=
      verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_computableInPolyTime
        W
    whenTrue :=
      verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_computableInPolyTime
        W
    whenFalse :=
      verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_computableInPolyTime
        W }
end CLRS.Chapter34.Turing.CookLevin
