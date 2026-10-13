import Mathlib

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω M : Type*} [MeasurableSpace M]

/-- The occupation measure `μ_t = (1/t) ∫_0^t δ_{x(s)} ds` of a path `x : ℝ≥0 → M` at time
`t > 0` (Benaïm 1999, §10, p. 61): the image of the uniform probability measure on `[0, t]` under
`s ↦ x(s)`, so that `μ_t(A) = (1/t) · Leb{s ∈ [0, t] : x(s) ∈ A}` for every Borel set `A`.
It is a Borel probability measure as soon as `x` is measurable and `t > 0`.

Totalisation: for `t = 0` (where `(1/t)∫_0^t` is undefined) and for a non-measurable path the
value is the Dirac mass `δ_{x(0)}`; the first case does not affect limit points as `t → ∞`, and
the second never arises for the paths of a progressively measurable process
(`IsProgressivelyMeasurable.measurable_path`). In particular the value is never the zero
measure. -/
noncomputable def occupationMeasure (x : ℝ≥0 → M) (t : ℝ≥0) : ProbabilityMeasure M :=
  open Classical in
  ⟨if Measurable x ∧ 0 < t then (volume[|Set.Icc (0 : ℝ) t]).map (fun s : ℝ => x s.toNNReal)
    else Measure.dirac (x 0), by
    split_ifs with h
    · have : IsProbabilityMeasure (volume[|Set.Icc (0 : ℝ) t]) :=
        cond_isProbabilityMeasure_of_finite
          (by simpa [Real.volume_Icc] using h.2.ne') (by simp [Real.volume_Icc])
      exact Measure.isProbabilityMeasure_map (h.1.comp measurable_real_toNNReal).aemeasurable
    · infer_instance⟩

/-- For a measurable path and `t > 0`, the occupation measure is the push-forward of the
normalised Lebesgue measure on `[0, t]`. -/
theorem coe_occupationMeasure {x : ℝ≥0 → M} (hx : Measurable x) {t : ℝ≥0} (ht : 0 < t) :
    (occupationMeasure x t : Measure M) =
      (volume[|Set.Icc (0 : ℝ) t]).map (fun s : ℝ => x s.toNNReal) := by
  have h : Measurable x ∧ 0 < t := ⟨hx, ht⟩
  simp only [occupationMeasure, ProbabilityMeasure.coe_mk]
  rw [if_pos h]

variable [TopologicalSpace M] [OpensMeasurableSpace M]

/-- The (possibly empty) set `𝓜(X, ω) ⊂ 𝓟(M)` of weak limit points of the occupation measures
`{μ_t(ω)}` of the path `t ↦ X(t, ω)` as `t → ∞` (Benaïm 1999, §10, p. 61): the cluster points of
`t ↦ μ_t(ω)` along `t → ∞` in the topology of weak convergence on `ProbabilityMeasure M`. -/
def occupationLimitPoints (X : ℝ≥0 → Ω → M) (ω : Ω) : Set (ProbabilityMeasure M) :=
  {μ | MapClusterPt μ atTop (fun t : ℝ≥0 => occupationMeasure (fun s => X s ω) t)}

end StochApproxDyn.WeakAPT
