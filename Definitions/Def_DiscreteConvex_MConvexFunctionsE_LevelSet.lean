import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The level set `L(f, α) = {x ∈ Zⱽ | f(x) ≤ α}`, Eq. (6.95). -/
def LevelSet (f : (V → ℤ) → WithTop ℝ) (alpha : ℝ) : Set (V → ℤ) :=
  {x | f x ≤ (alpha : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsE
