import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `F` is the negation of a `WithTop ℝ`-valued function satisfying `P`. -/
def IsNegOf (P : ((V → ℤ) → WithTop ℝ) → Prop) (F : (V → ℤ) → EReal) : Prop :=
  ∃ h : (V → ℤ) → WithTop ℝ, P h ∧ ∀ x, F x = -ToEReal (h x)

end DiscreteConvex.ConjugacyDualityD
