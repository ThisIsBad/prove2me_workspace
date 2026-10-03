import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.67 (p.170). Level-set characterizations of (QMw). -/
theorem qmw_level_characterizations (f : (V → ℤ) → WithTop ℝ) :
    [QMw f,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → max (f x) (f y) ≥ MinDownSym f x y,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → f x ≥ f y → f x ≥ MinDown f x y].TFAE := by sorry

end DiscreteConvex.MConvexFunctionsE
