import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Exact accumulated budget for scanning every row below one current row. -/
def compatibilityEdgesPriorRowsSteps
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : Nat :=
  (priors.map (compatibilityEdgesPriorRowSteps current)).sum
end TMClique
end Turing
end Chapter34
end CLRS
