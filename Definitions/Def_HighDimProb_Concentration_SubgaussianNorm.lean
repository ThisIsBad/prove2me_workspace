import Mathlib

open MeasureTheory

namespace HighDimProb.Concentration

/-- The sub-gaussian (Orlicz `ψ₂`) norm of a real random variable `X` on a probability
space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition 2.5.6 /
Eq. (2.13): the smallest `t > 0` such that the exponential moment `E[exp(X² / t²)]` is
*finite* and `≤ 2`, i.e.

`‖X‖_{ψ₂} := inf {t > 0 : exp(X² / t²) is integrable and E exp(X² / t²) ≤ 2}`.

The `Integrable` conjunct is essential: Mathlib's Bochner integral of a non-integrable
function is `0` by convention, so without it every `t` for which the moment is actually
infinite would vacuously satisfy `∫ … ≤ 2` and enter the infimum, collapsing the norm of
genuinely non-sub-gaussian (and even sub-gaussian) variables to `0`. If no `t` exists with
both conjuncts holding (`X` is not sub-gaussian), `sInf` of the empty set defaults to `0`,
Mathlib's usual junk value for an unbounded-below or empty set. -/
noncomputable def subgaussianNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P ∧
                ∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P ≤ 2}

end HighDimProb.Concentration
