import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Tagged physical family used by the restoration and emission phases. -/
def encodeTaggedOccurrenceEntries
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List UnaryFrameSym :=
  priors.flatMap (encodeTaggedOccurrenceEntry current)
end TMClique
end Turing
end Chapter34
end CLRS
