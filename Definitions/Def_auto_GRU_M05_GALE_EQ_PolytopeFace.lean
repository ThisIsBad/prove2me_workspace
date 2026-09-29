import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic
import Mathlib.Analysis.Convex.Intrinsic
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

abbrev PolytopeFace {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {F : Set (Fin d → ℝ) // IsExposed ℝ P F}

end Grunbaum2003
