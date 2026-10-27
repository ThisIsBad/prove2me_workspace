import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1A
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def compatibleOccurrencePairs
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List (Nat × Nat) :=
  priors.flatMap (compatibleOccurrencePair current)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
