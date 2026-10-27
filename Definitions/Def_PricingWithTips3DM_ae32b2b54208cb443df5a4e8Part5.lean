import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

noncomputable def rawPairs_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      certificateRawPairs := by
  let pairs := pairIterations_computableInPolyTime
  exact
    { tm := pairs.tm
      inputAlphabet := pairs.inputAlphabet
      outputAlphabet := pairs.outputAlphabet
      time := pairs.time
      outputsFun := fun vertices => by
        simpa [encodeCertificatePairIterations_eq] using
          pairs.outputsFun vertices }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
