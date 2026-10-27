import Definitions.Def_PricingWithTips3DM_bee5ca8bac6e3d05c7e8dd30
import Definitions.Def_PricingWithTips3DM_b6a60ccae73d200ecf9d427a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw verifier-symbol source for input-boundary arms

Unlike the preceding coordinate sources, this component depends on the actual
input symbols rather than only on the input length.  The verifier's fixed
alphabet code table is compiled into finite control and emits the exact unary
cell-code block for every public input symbol.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Natural code of one public verifier input symbol in the initial tableau
stack alphabet. -/
def verifierPublicInputCode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (symbol : Γ) : Nat :=
  (verifierInputCode W (some symbol)).val

/-- Exact delimiter-bearing code stream for every symbol of the raw word. -/
def verifierPublicInputCodeFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame (input.map (verifierPublicInputCode W))

/-- The generic bounded-loop symbol compiler has exactly the verifier-specific
cell-code semantics. -/
theorem verifierPublicInputCodeFrames_eq_finiteSymbolUnaryFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierPublicInputCodeFrames W input =
      finiteSymbolUnaryFrames (verifierPublicInputCode W) input := by
  exact (finiteSymbolUnaryFrames_eq_encodeUnaryFrame
    (verifierPublicInputCode W) input).symm

/-- One fixed polynomial-time TM2 reads the raw verifier word and emits all
of its exact initial-tableau cell codes. -/
noncomputable def verifierPublicInputCodeFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierPublicInputCodeFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let compiled := finiteSymbolUnaryFrames_computableInPolyTime
    (verifierPublicInputCode W)
  exact
    { tm := compiled.tm
      inputAlphabet := compiled.inputAlphabet
      outputAlphabet := compiled.outputAlphabet
      time := compiled.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierPublicInputCodeFrames_eq_finiteSymbolUnaryFrames W input]
          using compiled.outputsFun input }

end CLRS.Chapter34.Turing.CookLevin
