import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsDeltaFeasibleFlow
import Definitions.Def_DiscreteConvex_AlgorithmsB_AphiActive
import Definitions.Def_DiscreteConvex_AlgorithmsB_ZVec
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoArcsLeaving
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoActiveTriples

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.20 (p.297). GOAL. If `S⊆W⊆V∖T`, no arcs of the auxiliary network leave `W`,
and no active triple exists, then `z⁻(V) ≥ ρ(W)-nδ` and `x⁻(V) ≥ ρ(W)-n²δ`; moreover `W`
minimizes `ρ` once `δ` is smaller than the least positive gap between two values of `ρ`, scaled
by `n²`. -/
theorem approx_optimality_from_no_augmenting_path {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (delta : ℝ) (hdelta : 0 < delta)
    (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (W : Finset V)
    (hSW : ∀ v, ZVec x phi v ≤ -delta → v ∈ W) (hWT : ∀ v ∈ W, ¬ (delta ≤ ZVec x phi v))
    (hnoarcs : NoArcsLeaving (AphiActive phi) W) (hnoactive : NoActiveTriples I L W) :
    (∑ v, NegPart (ZVec x phi) v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ) * delta ∧
    (∑ v, NegPart x v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ)^2 * delta ∧
    (∀ Delta : ℝ, (∀ X Y : Finset V, (rho X : ℝ) - (rho Y : ℝ) > 0 → Delta ≤ (rho X : ℝ) - (rho Y : ℝ)) →
      delta < Delta / (Fintype.card V : ℝ)^2 → (rho W : ℤ) = MinRho rho) := by sorry

end DiscreteConvex.AlgorithmsB
