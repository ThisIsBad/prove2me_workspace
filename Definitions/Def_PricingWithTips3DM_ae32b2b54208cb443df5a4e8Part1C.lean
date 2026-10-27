import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1B
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def compatibleOccurrencePairIterations :
    List (IndexedOccurrence × Nat) → List (Nat × Nat)
  | [] => []
  | current :: priors =>
      compatibleOccurrencePairIterations priors ++
        compatibleOccurrencePairs current priors.reverse

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
