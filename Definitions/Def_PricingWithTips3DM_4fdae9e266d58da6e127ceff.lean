import Definitions.Def_PricingWithTips3DM_a1e492e117ae1c512cdc4f29
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: named configurations -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

abbrev stackContents (input : List NormalizedCircuitSym)
    (output : List FormulaSym) (inputCount saved : Nat) :
    ∀ stack : Stack, List (Alphabet stack)
  | .input => input
  | .output => output
  | .inputCount => List.replicate inputCount ()
  | .saved => List.replicate saved ()

def cfg (label : Option Label) (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) : reverseMachine.Cfg :=
  ⟨label, state, stackContents input output inputCount saved⟩

def step : reverseMachine.Cfg → Option reverseMachine.Cfg := reverseMachine.step

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
