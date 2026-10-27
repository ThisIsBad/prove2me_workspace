import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Fixed invocation delimiters -/

/-- Delimiter layout of one standalone runtime-stack invocation.  The
seventh zero field materializes the header boundary; the eighth height field
is the runtime payload terminated by the outer stack boundary. -/
def arithmeticValidityTailStackOperandDelimiters : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator,
    .separator, .separator, .frameEnd, .frameEnd]

/-- The four fixed final-conjunction prefix operands remain ordinary unary
blocks; the variable one-hot family follows them in the next source layer. -/
def arithmeticValidityTailFinalPrefixDelimiters : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator]

/-- One complete cyclic delimiter table for the fixed part of a validity-tail
row: one eight-field stack invocation per fixed machine stack, then the four
final-conjunction prefix fields. -/
def arithmeticValidityTailFixedOperandDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  ((arithmeticRuntimeStackSourceIndices tm).flatMap fun _ =>
      arithmeticValidityTailStackOperandDelimiters) ++
    arithmeticValidityTailFinalPrefixDelimiters

@[simp] theorem arithmeticValidityTailFixedOperandDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (arithmeticValidityTailFixedOperandDelimiters tm).length := by
  simp [arithmeticValidityTailFixedOperandDelimiters,
    arithmeticValidityTailFinalPrefixDelimiters]

/-- The delimiter table has exactly one entry for every fixed affine form. -/
theorem arithmeticValidityTailFixedOperandDelimiters_length
    (tm : _root_.Turing.FinTM2) :
    (arithmeticValidityTailFixedOperandDelimiters tm).length =
      (arithmeticValidityTailFixedOperandForms tm).length := by
  simp [arithmeticValidityTailFixedOperandDelimiters,
    arithmeticValidityTailStackOperandDelimiters,
    arithmeticValidityTailFinalPrefixDelimiters,
    arithmeticValidityTailFixedOperandForms,
    arithmeticValidityTailStackOperandFormsFamily,
    arithmeticValidityTailStackOperandForms,
    arithmeticValidityTailFinalPrefixForms, affineValidityForm]
end CLRS.Chapter34.Turing.CookLevin
