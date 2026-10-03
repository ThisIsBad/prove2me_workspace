import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.75 (p.173). Level-set characterizations of (SSQM≠_w). -/
theorem ssqmnew_level_characterizations (f : (V → ℤ) → WithTop ℝ) :
    [SSQMNeW f,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → max (f x) (f y) > MinDownSym f x y,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x > f y → f x > MinDown f x y].TFAE := by sorry

end DiscreteConvex.MConvexFunctionsE
