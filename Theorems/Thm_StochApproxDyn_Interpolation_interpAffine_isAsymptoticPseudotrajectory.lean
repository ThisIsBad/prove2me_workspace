import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_Interpolation_VectorFieldFlow
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, Proposition 4.1, first conclusion, pp. 12–13. Let `F : ℝ^d → ℝ^d` be continuous
and globally integrable, with flow `Φ`. Let `{x_n}` follow the recursion (7) with step sizes
satisfying the standing assumptions (`γ_n ≥ 0`, `Σ γ_n = ∞`, `γ_n → 0`). Assume A1 and either
A2 (`sup_n ‖x_n‖ < ∞`) or A2′ (`F` Lipschitz and bounded on a uniform neighbourhood of
`{x_n : n ≥ 0}`). Then the affine interpolated process `X` is an asymptotic pseudotrajectory of
`Φ`. -/
theorem interpAffine_isAsymptoticPseudotrajectory {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (hint : IsGloballyIntegrable F)
    (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : IsFlowOf F Φ)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (hA1 : SatisfiesA1 γ U)
    (hA2 : SatisfiesA2 x ∨ SatisfiesA2' F x) :
    IsAsymptoticPseudotrajectory Φ (fun t : ℝ≥0 => interpAffine γ x (t : ℝ)) := by sorry

end StochApproxDyn.Interpolation

