import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
namespace Grunbaum2003

/-- Full-dimensional nonempty polytopes in real coordinate space.
Grünbaum §3.1, p. 31: polytopes are equivalently finite convex hulls.
This is a local definition, not a published Prove2Me reference. -/
def IsDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V) ∧
    affineSpan ℝ P = ⊤

end Grunbaum2003
