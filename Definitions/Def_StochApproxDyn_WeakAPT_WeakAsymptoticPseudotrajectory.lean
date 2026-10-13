import Mathlib

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω M : Type*} {m0 : MeasurableSpace Ω}

/-- Progressive measurability (Benaïm 1999, §10, p. 61, condition (i)): for every `T > 0` the
restriction `X|[0, T] × Ω` is `𝓑_{[0,T]} × 𝓕_T`-measurable, where `𝓑_{[0,T]}` is the Borel
σ-field of `[0, T]`. -/
def IsProgressivelyMeasurable [MeasurableSpace M] (ℱ : Filtration ℝ≥0 m0)
    (X : ℝ≥0 → Ω → M) : Prop :=
  ∀ T : ℝ≥0, 0 < T →
    Measurable[(inferInstance : MeasurableSpace (Icc (0 : ℝ≥0) T)).prod (ℱ T)]
      (fun p : Icc (0 : ℝ≥0) T × Ω => X p.1 p.2)

/-- Every path `t ↦ X(t, ω)` of a progressively measurable process is Borel measurable. -/
theorem IsProgressivelyMeasurable.measurable_path [MeasurableSpace M] {ℱ : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → M} (hX : IsProgressivelyMeasurable ℱ X) (ω : Ω) :
    Measurable (fun s => X s ω) := by
  have hr : ∀ n : ℕ, Measurable (fun s : Icc (0 : ℝ≥0) ((n : ℝ≥0) + 1) => X s ω) := by
    intro n
    have h := hX ((n : ℝ≥0) + 1) (by positivity)
    have hm : Measurable[_, (inferInstance : MeasurableSpace (Icc (0 : ℝ≥0) ((n : ℝ≥0) + 1))).prod
        (ℱ ((n : ℝ≥0) + 1))] (fun s : Icc (0 : ℝ≥0) ((n : ℝ≥0) + 1) => (s, ω)) :=
      @measurable_prodMk_right _ _ _ (ℱ _) ω
    exact h.comp hm
  intro B hB
  have : (fun s => X s ω) ⁻¹' B = ⋃ n : ℕ, Subtype.val ''
      ((fun s : Icc (0 : ℝ≥0) ((n : ℝ≥0) + 1) => X s ω) ⁻¹' B) := by
    ext s
    simp only [mem_preimage, mem_iUnion, mem_image, Subtype.exists, mem_Icc, exists_and_right,
      exists_eq_right]
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_ge s
      exact ⟨n, ⟨zero_le, hn.trans (le_add_of_nonneg_right zero_le_one)⟩, hs⟩
    · rintro ⟨n, _, hs⟩; exact hs
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_Icc.subtype_image (hr n hB)

/-- The deviation event
`{ω : sup_{0 ≤ h ≤ T} d(X(t + h, ω), Φ_h(X(t, ω))) ≥ α}` of condition (ii)
(Benaïm 1999, §10, p. 61). Paths need not be continuous, so the supremum is taken in `[0, ∞]`
(via the extended distance `edist`), where it always exists. -/
def deviationEvent [PseudoMetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (t : ℝ≥0) (α : ℝ) (T : ℝ≥0) : Set Ω :=
  {ω | ENNReal.ofReal α ≤ ⨆ h ∈ Icc (0 : ℝ≥0) T, edist (X (t + h) ω) (Φ h (X t ω))}

/-- A **weak asymptotic pseudotrajectory** of the semiflow `Φ` (Benaïm 1999, §10, p. 61): on a
probability space `(Ω, 𝓕, P)` with a nondecreasing family `{𝓕_t}_{t ≥ 0}` of sub-σ-algebras, a
process `X : ℝ₊ × Ω → M` such that
(i) `X` is progressively measurable, and
(ii) `lim_{t → ∞} P{sup_{0 ≤ h ≤ T} d(X(t + h), Φ_h(X(t))) ≥ α | 𝓕_t} = 0` almost surely, for
each `α > 0` and `T > 0`.
The conditional probability is `P[1_A | 𝓕_t]`, the conditional expectation of the indicator of
the deviation event `A`. The paper writes `P{A | 𝓕_t}`, which presupposes that `A` is an event;
this is recorded as the explicit field `measurableSet_deviation` (without it, Mathlib's
conditional expectation of a non-measurable indicator would be `0` and (ii) would be vacuous). -/
structure IsWeakAsymptoticPseudotrajectory [PseudoMetricSpace M] [MeasurableSpace M]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 m0) (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M) : Prop where
  /-- Condition (i): progressive measurability. -/
  progMeasurable : IsProgressivelyMeasurable ℱ X
  /-- The deviation sets of condition (ii) are events. -/
  measurableSet_deviation :
    ∀ (t : ℝ≥0) (α : ℝ) (T : ℝ≥0), 0 < α → 0 < T → MeasurableSet (deviationEvent Φ X t α T)
  /-- Condition (ii). -/
  tendsto_condProb : ∀ (α : ℝ) (T : ℝ≥0), 0 < α → 0 < T →
    ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ≥0 => (P[(deviationEvent Φ X t α T).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω)
      atTop (𝓝 0)

end StochApproxDyn.WeakAPT
