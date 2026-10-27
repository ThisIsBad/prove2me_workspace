import Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

theorem replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

theorem separator_replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    (.separator :: List.replicate count .tick) ++ .tick :: tail =
      (.separator :: List.replicate (count + 1) .tick) ++ tail := by
  simp only [List.cons_append, replicate_tick_append_tick]

inductive CompatibilityRestoreField
  | variable | polarity | clause
  deriving DecidableEq

def compatibilityRestoreFieldLabel :
    CompatibilityRestoreField → CompatibilityEdgesLabel
  | .variable => .taggedRestoreVariable
  | .polarity => .taggedRestorePolarity
  | .clause => .taggedRestoreClause

def compatibilityRestoreFieldNext :
    CompatibilityRestoreField → CompatibilityEdgesLabel
  | .variable => .taggedRestorePolarity
  | .polarity => .taggedRestoreClause
  | .clause => .taggedRestoreVertex
end TMClique
end Turing
end Chapter34
end CLRS
