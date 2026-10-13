import Mathlib

namespace TsitsiklisGittins.IndexTheorem

/-- Equation (2.2) of Tsitsiklis (1994), p. 196: with `τ` the (possibly infinite) first time bandit
`i*` is played, `T` the duration `T(s*)` of a play at `s*`, `r̄(t)` the reward rate under the
policy at time `t` and `r̄(t) ≤ r(s*)` for all `t`,
`E[(1 − e^{−βτ}) ∫₀^{T(s*)} r(s*) e^{−βt} dt] ≥ E[(1 − e^{−βT(s*)}) ∫₀^τ r̄(t) e^{−βt} dt]`.
Here `e^{−β·∞} = 0` and `∫₀^∞` is the integral over `(0, ∞)`. -/
theorem eq2_2_interchange_inequality {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (β : ℝ) (hβ : 0 < β)
    (T : Ω → ℝ) (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω)
    (τ : Ω → ENNReal) (hτ : Measurable τ)
    (rbar : Ω → ℝ → ℝ) (hrbar : Measurable (Function.uncurry rbar))
    (C : ℝ) (hC : ∀ ω t, |rbar ω t| ≤ C)
    (rstar : ℝ) (hle : ∀ ω t, rbar ω t ≤ rstar) :
    ∫ ω, (1 - (if τ ω = ⊤ then 0 else Real.exp (-(β * (τ ω).toReal)))) *
          (∫ t in (0 : ℝ)..T ω, rstar * Real.exp (-(β * t))) ∂P ≥
      ∫ ω, (1 - Real.exp (-(β * T ω))) *
          (∫ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < τ ω}, rbar ω t * Real.exp (-(β * t))) ∂P := by sorry

end TsitsiklisGittins.IndexTheorem

