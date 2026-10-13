import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, §4.1, Eq. (9), p. 12: under the standing assumptions on `γ` and the recursion (7),
the affine interpolated process solves the integral form of (7):
`X(t) − X(0) = ∫_0^t [F(X̄(s)) + Ū(s)] ds` for every `t ≥ 0`. -/
theorem interpAffine_sub_eq_integral {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (t : ℝ) (ht : 0 ≤ t) :
    interpAffine γ x t - interpAffine γ x 0 =
      ∫ s in (0 : ℝ)..t, (F (interpConst γ x s) + noiseInterp γ U s) := by sorry

end StochApproxDyn.Interpolation

