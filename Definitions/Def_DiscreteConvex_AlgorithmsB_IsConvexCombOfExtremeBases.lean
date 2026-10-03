import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExtremeBaseVec

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `x` is represented as a convex combination `Σ λᵢyᵢ` of extreme bases (Eq. (10.13)). -/
def IsConvexCombOfExtremeBases {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ) : Prop :=
  (∀ i ∈ I, 0 ≤ lam i) ∧ (∑ i ∈ I, lam i = 1) ∧
    (∀ v, x v = ∑ i ∈ I, lam i * (ExtremeBaseVec rho (L i) v : ℝ))

-- ===== δ-feasible flows and the auxiliary network (§10.2.3) =====

end DiscreteConvex.AlgorithmsB
