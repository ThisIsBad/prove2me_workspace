import Definitions.Def_PricingWithTips3DM_587002a90801ede7195efef5
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Occurrence compatibility edges: all prior rows

This file iterates the verified one-row scan across the complete family below
one current occurrence.  The resulting reversed rows carry their exact
compatibility tags and the controller reaches the counter-cleanup boundary.
-/

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- One reversed prior row together with its compatibility tag. -/
def encodeTaggedOccurrenceEntry
    (current prior : IndexedOccurrence × Nat) : List UnaryFrameSym :=
  encodeCompatibilityTag (indexedOccurrencesCompatibleCode current prior) ++
    (encodeIndexedOccurrenceEntry prior).reverse
end TMClique
end Turing
end Chapter34
end CLRS
