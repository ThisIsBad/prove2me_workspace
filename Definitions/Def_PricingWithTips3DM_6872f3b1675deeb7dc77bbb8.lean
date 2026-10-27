import Definitions.Def_PricingWithTips3DM_af4f7f7eb260f6bfe78aaf7b
import Definitions.Def_PricingWithTips3DM_9a3f6d04d98bfcc3d719183a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Canonical widths of terminal stack value routes

Every per-stack terminal route has the same length as its canonical tableau
stack block.  Thus the remaining source compiler may stream fixed-width stack
blocks without depending on the particular push/pop path selected by a label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- The list of routed stack-block lengths is exactly the list of canonical
tableau stack widths, in the same fixed machine-stack order. -/
theorem TransitionStmtTerminalRowLayout.stackValueRouteValues_map_length
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    (layout.stackValueRouteValues tm start height falseWire trueWire source).map
        List.length =
      (arithmeticRuntimeStackSourceIndices tm).map fun position =>
        cfgStackBitWidth tm height
          ((arithmeticStackEquiv tm).symm position) := by
  unfold TransitionStmtTerminalRowLayout.stackValueRouteValues
    TransitionStmtTerminalRowLayout.stackValueBlocks
  simp only [List.map_map]
  apply List.map_congr_left
  intro position hposition
  let k := (arithmeticStackEquiv tm).symm position
  let block := transitionStmtSelectedStackActionValues_eval tm k start height
    falseWire trueWire (TransitionStackValueBlock.ofWires (source.stack k))
    (transitionStmtStackActionsFor tm k layout.stackActions)
  change block.flatten.length = cfgStackBitWidth tm height k
  apply TransitionStackValueBlock.HasShape.flatten_length_eq_cfgStackBitWidth
  apply transitionStmtSelectedStackActionValues_eval_hasShape
  exact TransitionStackValueBlock.hasShape_ofWires tm k height
    (source.stack k)

end CLRS.Chapter34.Turing.CookLevin
