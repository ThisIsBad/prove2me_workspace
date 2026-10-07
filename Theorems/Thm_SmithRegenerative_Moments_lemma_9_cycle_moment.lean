import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 28, Lemma 9.
Formalization Note: the paper writes `Ey₁^p` for a real `p > 0` without saying
`y₁ ≥ 0`; its proof integrates from `0−`, i.e. treats a nonnegative cycle
quantity. The statement is taken for `|y_n|^p`, which is the printed lemma when
`y ≥ 0` and the meaningful `p`th moment for a signed `y`. Theorem 8 applies it to
the cumulative process `w̃` (whose cycle increments are the `ỹ_n ≥ 0`).
`y_{n_t}` is the increment of cycle `n_t`, the cycle `[T_{n_t-1}, T_{n_t})`
containing `t`. -/
theorem lemma_9_cycle_moment {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω) (p : ℝ) (hp : 0 < p)
    (hκp : Integrable
      (fun ω => |cycleReward C.renewal C.w 1 ω| ^ p) C.renewal.P) :
    (∀ t : ℝ, 0 ≤ t → Integrable
      (fun ω => |cycleReward C.renewal C.w (C.renewal.count t ω) ω| ^ p)
        C.renewal.P) ∧
    (fun t : ℝ =>
      ∫ ω, |cycleReward C.renewal C.w (C.renewal.count t ω) ω| ^ p
        ∂C.renewal.P) =o[atTop] (fun t : ℝ => t) := by sorry

end SmithRegenerative.Moments

