import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- A spectrally negative Lévy process started at `0` (Avram–Kyprianou–Pistorius 2004, §2, p. 216).
Time is `ℝ≥0`, values are real. The fields are:
* each `X t` is measurable;
* every path starts at `0`;
* independent increments (Mathlib's `HasIndepIncrements`);
* stationary increments: `X (s + t) - X s` has the law of `X t`;
* every path is right-continuous at every time and has a left limit at every `t > 0` (càdlàg);
* no positive jumps: for every path and every `t > 0`, `X t ≤ X (t-)`;
* the paths are not almost surely monotone ("We exclude the case that X has monotone paths"):
  neither almost surely nondecreasing nor almost surely nonincreasing. -/
structure IsSNLevy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable (X t)
  start_zero : ∀ ω, X 0 ω = 0
  indep_increments : HasIndepIncrements X P
  stationary_increments :
    ∀ s t : ℝ≥0, IdentDistrib (fun ω => X (s + t) ω - X s ω) (X t) P P
  right_continuous : ∀ ω (t : ℝ≥0), ContinuousWithinAt (fun r => X r ω) (Set.Ici t) t
  left_limits : ∀ ω (t : ℝ≥0), 0 < t →
    ∃ l : ℝ, Filter.Tendsto (fun r => X r ω) (nhdsWithin t (Set.Iio t)) (nhds l)
  no_positive_jumps : ∀ ω (t : ℝ≥0), 0 < t → X t ω ≤ Function.leftLim (fun r => X r ω) t
  not_ae_monotone : ¬ (∀ᵐ ω ∂P, Monotone fun t => X t ω)
  not_ae_antitone : ¬ (∀ᵐ ω ∂P, Antitone fun t => X t ω)

end Avram2004.Exit
