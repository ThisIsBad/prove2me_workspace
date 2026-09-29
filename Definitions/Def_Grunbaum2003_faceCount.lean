import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

noncomputable def faceCount {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) : ℕ :=
  {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

end Grunbaum2003
