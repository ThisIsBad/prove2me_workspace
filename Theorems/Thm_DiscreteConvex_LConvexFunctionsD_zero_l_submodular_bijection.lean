import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRho
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRhoZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.40 (p.195). The one-to-one correspondence between positively homogeneous L-convex
functions and submodular set functions. -/
theorem zero_l_submodular_bijection :
    (∀ g : (V → ℝ) → WithTop ℝ, ZeroLR g → LovaszExtension (InducedRho g) = g) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → InducedRho (LovaszExtension rho) = rho) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, ZeroLZZ g →
      (fun p : V → ℤ => LovaszExtension (InducedRhoZ g) (fun v => (p v : ℝ))) = g) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → IsIntegerValued rho →
      InducedRhoZ (fun p : V → ℤ => LovaszExtension rho (fun v => (p v : ℝ))) = rho) := by sorry

end DiscreteConvex.LConvexFunctionsD
