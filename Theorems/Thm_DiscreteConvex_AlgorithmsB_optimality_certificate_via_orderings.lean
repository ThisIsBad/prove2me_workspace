import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPosR
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNegR
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrecedesIn
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.9 (p.289). A sufficient condition for optimality in (10.11), stated in terms
of the linear orderings representing a base as a convex combination of extreme bases. -/
theorem optimality_certificate_via_orderings {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (W : Finset V) :
    ((∀ v ∈ SuppNegR' x, v ∈ W) ∧ (∀ v ∈ SuppPosR' x, v ∉ W) →
      ∑ v, NegPart x v = ∑ v ∈ W, x v) ∧
    ((∀ i ∈ I, ∀ u ∈ W, ∀ v ∉ W, PrecedesIn (L i) u v) → ∑ v ∈ W, x v = (rho W : ℝ)) ∧
    (((∀ v ∈ SuppNegR' x, v ∈ W) ∧ (∀ v ∈ SuppPosR' x, v ∉ W)) →
      (∀ i ∈ I, ∀ u ∈ W, ∀ v ∉ W, PrecedesIn (L i) u v) →
      ∑ v, NegPart x v = (MinRho rho : ℝ) ∧ (rho W : ℤ) = MinRho rho) := by sorry

end DiscreteConvex.AlgorithmsB
