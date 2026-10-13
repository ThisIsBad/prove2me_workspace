import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- The event `{ω | sup_{s ≥ t} sup_{0 ≤ h ≤ T} d(X(s+h), Φ_h(X(s))) ≥ δ}` of (24) (Benaïm 1999,
p. 30), with the double supremum computed in `ℝ≥0∞` (so it may be `∞`). -/
def deviationEvent {Ω M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (t δ T : ℝ≥0) : Set Ω :=
  {ω | (δ : ℝ≥0∞) ≤ ⨆ (s : ℝ≥0) (_ : t ≤ s) (h : ℝ≥0) (_ : h ≤ T),
      edist (X (s + h) ω) (Φ h (X s ω))}

/-- The standing assumptions of Section 7 (p. 30). `X` is a continuous-time process on the
probability space `(Ω, 𝓕, P)` with continuous paths in `M`, adapted to the filtration `ℱ`, and for
all `δ > 0`, `T > 0`, `t ≥ 0`
`P(sup_{s≥t} sup_{0≤h≤T} d(X(s+h), Φ_h(X(s))) ≥ δ | ℱ_t) ≤ w(t, δ, T)`   (24)
for a function `w : ℝ₊³ → ℝ₊` with `w(t, δ, T) ↓ 0` as `t → ∞` (nonincreasing in `t`, limit `0`).
The conditional probability is the conditional expectation of the indicator of the event; that
event is required to be measurable (field `measurableSet_deviationEvent`). -/
structure SatisfiesStandingAssumption {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [MeasurableSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω) (ℱ : Filtration ℝ≥0 m0)
    (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) : Prop where
  continuous_path : ∀ ω, Continuous (fun t => X t ω)
  adapted : ∀ t, Measurable[ℱ t] (X t)
  measurableSet_deviationEvent :
    ∀ t δ T : ℝ≥0, 0 < δ → 0 < T → MeasurableSet (deviationEvent Φ X t δ T)
  condProb_le : ∀ t δ T : ℝ≥0, 0 < δ → 0 < T →
    P[(deviationEvent Φ X t δ T).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P]
      fun _ => (w t δ T : ℝ)
  antitone_w : ∀ δ T : ℝ≥0, 0 < δ → 0 < T → Antitone (fun t => w t δ T)
  tendsto_w : ∀ δ T : ℝ≥0, 0 < δ → 0 < T →
    Filter.Tendsto (fun t => w t δ T) Filter.atTop (nhds 0)

/-- `Att(X)`, the set of points attainable by `X` (p. 31): `p` is attainable if for each `t > 0`
and every open neighbourhood `U` of `p`, `P(∃ s ≥ t : X(s) ∈ U) > 0`. -/
def attainableSet {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] (P : Measure Ω)
    (X : ℝ≥0 → Ω → M) : Set M :=
  {p | ∀ t : ℝ≥0, 0 < t → ∀ U : Set M, IsOpen U → p ∈ U →
    0 < P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U}}

end StochApproxDyn.Attractor
