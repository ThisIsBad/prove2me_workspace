import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_BasePolyhedronR
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.8 (p.288). The min-max relation `max{x⁻(V) | x∈B(ρ)} = min{ρ(X) | X⊆V}`; if
`ρ` is integer valued the maximizer can be chosen integral. -/
theorem base_polyhedron_min_max (rho : Finset V → ℤ) (hrho : Submodular rho) :
    IsGreatest {t : ℝ | ∃ x : V → ℝ, BasePolyhedronR rho x ∧ t = ∑ v, NegPart x v}
      ((MinRho rho : ℝ)) ∧
    ∃ x : V → ℤ, (∀ X : Finset V, ∑ v ∈ X, (x v : ℝ) ≤ (rho X : ℝ)) ∧
      (∑ v, (x v : ℝ) = (rho Finset.univ : ℝ)) ∧
      (∑ v, NegPart (fun v => (x v : ℝ)) v = (MinRho rho : ℝ)) := by sorry

end DiscreteConvex.AlgorithmsB
