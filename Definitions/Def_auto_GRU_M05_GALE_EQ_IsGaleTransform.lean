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

def IsGaleTransform {d n : ℕ} (V : Fin n → (Fin d → ℝ))
    (G : Fin n → (Fin (n - d - 1) → ℝ)) : Prop :=
  LinearIndependent ℝ (fun j : Fin (n - d - 1) => fun i : Fin n => G i j) ∧
    (Submodule.span ℝ
      (Set.range (fun j : Fin (n - d - 1) => fun i : Fin n => G i j)) :
        Set (Fin n → ℝ)) =
      {a | (∑ i, a i) = 0 ∧ (∑ i, a i • V i) = 0}

end Grunbaum2003
