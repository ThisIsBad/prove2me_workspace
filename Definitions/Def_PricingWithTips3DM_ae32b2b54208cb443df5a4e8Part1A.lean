import Definitions.Def_PricingWithTips3DM_88801654eeed9b1dbb21ce0f
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def compatibleOccurrencePair
    (current prior : IndexedOccurrence × Nat) : List (Nat × Nat) :=
  if TMClique.indexedOccurrencesCompatibleCode current prior then
    [(prior.2, current.2)]
  else []

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
