import Definitions.Def_PricingWithTips3DM_88801654eeed9b1dbb21ce0f
import Mathlib.Tactic.DeriveFintype
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
open PolyBuilder

inductive EndpointOrder
  | leftLess | equal | rightLess
deriving DecidableEq, Fintype

def normalizeQuery (edge : Nat × Nat) : Nat × Nat :=
  if edge.1 ≤ edge.2 then edge else (edge.2, edge.1)

def encodeNormalizedQueries (edges : List (Nat × Nat)) : List CliqueSym :=
  edges.flatMap (encodeCliqueEdge ∘ normalizeQuery)

inductive Label
  | scan | left | incrementLeft | right | incrementRight
  | compareLeft | compareRight | saveMatched | probeRight
  | restoreMatched (order : EndpointOrder)
  | restoreLeft (order : EndpointOrder)
  | restoreRight (order : EndpointOrder)
  | restoreExtraLeft | restoreExtraRight
  | pushEdgeMark (order : EndpointOrder)
  | lower (order : EndpointOrder) | pushLowerTick (order : EndpointOrder)
  | pushPairSeparator (order : EndpointOrder)
  | upper (order : EndpointOrder) | pushUpperTick (order : EndpointOrder)
  | pushRecordEnd | halt | invalid
deriving DecidableEq, Fintype

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
