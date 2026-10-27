import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def certificateRawPairs (vertices : List Nat) : List (Nat × Nat) :=
  compatibleOccurrencePairIterations (certificatePairEntries vertices).reverse

theorem encodeCertificatePairIterations_eq (vertices : List Nat) :
    encodeCertificatePairIterations vertices =
      (certificateRawPairs vertices).flatMap encodeCliqueEdge := by
  exact encodeCompatibleOccurrencePairIterations _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
