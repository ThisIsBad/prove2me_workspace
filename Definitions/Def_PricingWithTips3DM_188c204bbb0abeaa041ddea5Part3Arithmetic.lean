import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

theorem PricingWithTips3DM_outer_iteration_three_fields
    {clause variableCode vertex bound : Nat}
    (hclause : clause ≤ bound) (hvariable : variableCode ≤ bound)
    (hvertex : vertex ≤ bound) :
    1 + (clause + variableCode + 2) + vertex + 3 ≤ 3 * bound + 6 := by
  omega
