import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The "usual hypotheses" on a filtered probability space (Antonelli 1993, p. 777):
the filtration is right-continuous, and `𝓕 0` contains every `P`-null set
(`P s` is the outer measure, so subsets of null sets are included). -/
def UsualHypotheses (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  𝓕.rightCont ≤ 𝓕 ∧ ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

/-- An adapted process of bounded variation on `[0, T]` (the integrators `A`, `C` of §§2–3),
carried together with its minimal (Jordan) decomposition `A = A⁺ - A⁻`:
`A⁺`, `A⁻` are adapted, nondecreasing, right-continuous, vanish at `0`, are frozen after `T`,
`A⁺_t + A⁻_t` is the total variation `|A|_t` of `A` on `[0, t]`, and `|A|_T ≤ β`. -/
structure BVIntegrator (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) where
  /-- The process `A`. -/
  A : ℝ≥0 → Ω → ℝ
  /-- The positive variation `A⁺`. -/
  Apos : ℝ≥0 → Ω → ℝ
  /-- The negative variation `A⁻`. -/
  Aneg : ℝ≥0 → Ω → ℝ
  adapted : StronglyAdapted 𝓕 A
  adapted_pos : StronglyAdapted 𝓕 Apos
  adapted_neg : StronglyAdapted 𝓕 Aneg
  decomp : ∀ t ω, A t ω = Apos t ω - Aneg t ω
  mono_pos : ∀ ω, Monotone (fun t => Apos t ω)
  mono_neg : ∀ ω, Monotone (fun t => Aneg t ω)
  rc_pos : ∀ ω t, ContinuousWithinAt (fun s => Apos s ω) (Set.Ici t) t
  rc_neg : ∀ ω t, ContinuousWithinAt (fun s => Aneg s ω) (Set.Ici t) t
  zero : ∀ ω, Apos 0 ω = 0 ∧ Aneg 0 ω = 0
  frozen : ∀ ω t, T ≤ t → Apos t ω = Apos T ω ∧ Aneg t ω = Aneg T ω
  minimal : ∀ ω, ∀ t ≤ T,
    ENNReal.ofReal (Apos t ω + Aneg t ω) = eVariationOn (fun s => A s ω) (Set.Icc 0 t)
  bound : ∀ ω, Apos T ω + Aneg T ω ≤ β

namespace BVIntegrator

variable {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {β : ℝ}

/-- The total variation process `|A|_t = A⁺_t + A⁻_t`. -/
def totVar (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : ℝ := I.Apos t ω + I.Aneg t ω

/-- The Stieltjes measure `dA⁺(ω)` on `ℝ` of the path `x ↦ A⁺_{x⁺}(ω)`. -/
noncomputable def posMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  (show Monotone (fun x : ℝ => I.Apos x.toNNReal ω) from
    fun _ _ h => I.mono_pos ω (Real.toNNReal_le_toNNReal h)).stieltjesFunction.measure

/-- The Stieltjes measure `dA⁻(ω)` on `ℝ` of the path `x ↦ A⁻_{x⁺}(ω)`. -/
noncomputable def negMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  (show Monotone (fun x : ℝ => I.Aneg x.toNNReal ω) from
    fun _ _ h => I.mono_neg ω (Real.toNNReal_le_toNNReal h)).stieltjesFunction.measure

/-- The variation measure `|dA|(ω) = dA⁺(ω) + dA⁻(ω)`. -/
noncomputable def varMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  I.posMeasure ω + I.negMeasure ω

/-- The pathwise Lebesgue–Stieltjes integral `∫_s^t h_r dA_r` over `(s, t]`. -/
noncomputable def integral (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ω : Ω) : ℝ :=
  (∫ r in Set.Ioc (s : ℝ) (t : ℝ), h r.toNNReal ω ∂I.posMeasure ω) -
    ∫ r in Set.Ioc (s : ℝ) (t : ℝ), h r.toNNReal ω ∂I.negMeasure ω

/-- The pathwise integral `∫_s^t |h_r| |dA_r|` over `(s, t]`, in `[0, ∞]`. -/
noncomputable def absLIntegral (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc (s : ℝ) (t : ℝ), ‖h r.toNNReal ω‖ₑ ∂I.varMeasure ω

end BVIntegrator

end AntonelliBFSDE.BackwardForward
