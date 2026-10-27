import Definitions.Def_PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
open PolyBuilder

def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (left right scratch : List Unit) :
    BuilderCfg revProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := left
  counter₂ := right
  counter₃ := scratch

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
