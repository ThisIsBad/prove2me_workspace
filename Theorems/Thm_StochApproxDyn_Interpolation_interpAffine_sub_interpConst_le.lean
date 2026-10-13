import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, proof of Proposition 4.1, p. 13: if `‖F(x_n)‖ ≤ K` for all `n`, then for all `t`
large enough (with `t ≥ 1`) and every `T > 0`,
`sup_{t≤u≤t+T} ‖X(u) − X̄(u)‖ ≤ 2Δ(t − 1, T + 1) + sup_{t≤u≤t+T} K γ̄(u)`.
The threshold does not depend on `T`. -/
theorem interpAffine_sub_interpConst_le {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ) (x U : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : SatisfiesScheme F γ x U) (K : ℝ) (hK : ∀ n : ℕ, ‖F (x n)‖ ≤ K) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ T : ℝ, 0 < T → ∀ u ∈ Set.Icc t (t + T),
      ‖interpAffine γ x u - interpConst γ x u‖ ≤
        2 * Delta γ U (t - 1) (T + 1) +
          sSup ((fun v => K * stepInterp γ v) '' Set.Icc t (t + T)) := by sorry

end StochApproxDyn.Interpolation

