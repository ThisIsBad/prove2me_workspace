import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.6 (Integrality; p.252). Suppose MCFP0 has an optimal solution. (1) Primal
integrality: integer data give an integer-valued optimal flow. (2) Dual integrality: the set of
optimal potentials is an L-convex polyhedron, integral (with an integer-valued optimal potential)
when the cost vector is integer valued. The general clause is in the real class `L⁰[R]`, not the
integral hull class `L⁰[Z|R]`: one arc from `u` to `v` with capacities `0, 1`, cost `1/2` and zero
supply has optimal potentials `{p : p(v) - p(u) ≤ 1/2}`, the convex hull of no integer set. -/
theorem mcfp0_integrality (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (hopt : ∃ xi, OptimalFlowMCFP0 tail head cUpper cLower gamma x xi) :
    ((∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ)) ∧
      (∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ)) ∧
      (∀ v, ∃ n : ℤ, x v = (n:ℝ)) →
        ∃ xiZ : A → ℤ, OptimalFlowMCFP0 tail head cUpper cLower gamma x (fun a => (xiZ a : ℝ))) ∧
    LConvexPolyhedronR (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
    ((∀ a, ∃ n : ℤ, gamma a = (n:ℝ)) →
      IsIntegralPolyhedron (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) := by sorry

end DiscreteConvex.NetworkFlowsB

