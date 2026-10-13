import Mathlib

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- The "usual hypotheses" on a filtered probability space (Antonelli 1993, p. 777, after
Protter 1990): the filtration is right-continuous (`𝓕_{t+} ⊆ 𝓕_t`) and `𝓕_0` contains every
`P`-null set (`P s` is the outer measure, so subsets of null sets are included). -/
def UsualHypotheses {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  (∀ t : ℝ≥0, ∀ s : Set Ω, (∀ u : ℝ≥0, t < u → MeasurableSet[𝓕 u] s) → MeasurableSet[𝓕 t] s) ∧
    ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

/-- A path `x : ℝ≥0 → ℝ` is càdlàg on `[0, T]`: right-continuous at every `t < T` and with a
finite left limit at every `0 < t ≤ T`. -/
def IsCadlagOn (x : ℝ≥0 → ℝ) (T : ℝ≥0) : Prop :=
  (∀ t : ℝ≥0, t < T → ContinuousWithinAt x (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → t ≤ T → ∃ l : ℝ, Tendsto x (𝓝[<] t) (𝓝 l)

/-- A path `x : ℝ≥0 → ℝ` is càdlàg on `[0, ∞)`. -/
def IsCadlag (x : ℝ≥0 → ℝ) : Prop :=
  ∀ t : ℝ≥0, ContinuousWithinAt x (Set.Ici t) t ∧ (0 < t → ∃ l : ℝ, Tendsto x (𝓝[<] t) (𝓝 l))

/-- The Lebesgue–Stieltjes measure `dc` on `ℝ` of a nondecreasing path `c : ℝ≥0 → ℝ`, extended
to `ℝ` by `x ↦ c (max x 0)` (constant on `(-∞, 0]`, so `dc` has no mass on `(-∞, 0]`).
`Monotone.stieltjesFunction` uses the right limits of the path, which are the path itself when it
is right-continuous. For a path that is not nondecreasing the value is the zero measure (junk);
every use below assumes monotonicity. -/
noncomputable def stieltjesMeasureOf (c : ℝ≥0 → ℝ) : Measure ℝ := by
  classical
  exact if h : Monotone c then
    (h.comp (fun _ _ hxy => Real.toNNReal_mono hxy) :
      Monotone fun x : ℝ => c x.toNNReal).stieltjesFunction.measure
  else 0

/-- The integrator `A` of §2 (p. 778–779): an adapted process of bounded total variation with
`A_0 = 0` and `|A|_T ≤ β`, carried together with its minimal (Jordan) decomposition
`A = A⁺ - A⁻`, `|A| = A⁺ + A⁻`. Paths are right-continuous (Protter's convention), and only
`[0, T]` matters: `A⁺`, `A⁻` are frozen after `T`. -/
structure BVIntegrator {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (T β : ℝ≥0) where
  /-- The integrator `A`. -/
  A : ℝ≥0 → Ω → ℝ
  /-- The positive variation `A⁺`. -/
  Apos : ℝ≥0 → Ω → ℝ
  /-- The negative variation `A⁻`. -/
  Aneg : ℝ≥0 → Ω → ℝ
  adapted_A : StronglyAdapted 𝓕 A
  adapted_pos : StronglyAdapted 𝓕 Apos
  adapted_neg : StronglyAdapted 𝓕 Aneg
  decomp : ∀ t ω, A t ω = Apos t ω - Aneg t ω
  mono_pos : ∀ ω, Monotone fun t => Apos t ω
  mono_neg : ∀ ω, Monotone fun t => Aneg t ω
  rc_pos : ∀ ω t, ContinuousWithinAt (fun s => Apos s ω) (Set.Ici t) t
  rc_neg : ∀ ω t, ContinuousWithinAt (fun s => Aneg s ω) (Set.Ici t) t
  zero : ∀ ω, Apos 0 ω = 0 ∧ Aneg 0 ω = 0
  frozen : ∀ ω t, T ≤ t → Apos t ω = Apos T ω ∧ Aneg t ω = Aneg T ω
  minimal : ∀ ω, ∀ t ≤ T,
    ENNReal.ofReal (Apos t ω + Aneg t ω) = eVariationOn (fun s => A s ω) (Set.Icc 0 t)
  bound : ∀ ω, Apos T ω + Aneg T ω ≤ β

namespace BVIntegrator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {T β : ℝ≥0}

/-- The total variation process `|A|_t = A⁺_t + A⁻_t`. -/
def totVar (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : ℝ := I.Apos t ω + I.Aneg t ω

/-- The Stieltjes measure `dA⁺(ω)` on `ℝ`. -/
noncomputable def posMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  stieltjesMeasureOf fun t => I.Apos t ω

/-- The Stieltjes measure `dA⁻(ω)` on `ℝ`. -/
noncomputable def negMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  stieltjesMeasureOf fun t => I.Aneg t ω

/-- The variation measure `|dA(ω)| = dA⁺(ω) + dA⁻(ω)`. -/
noncomputable def varMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  I.posMeasure ω + I.negMeasure ω

/-- The pathwise Lebesgue–Stieltjes integral `∫_s^t h_r dA_r` over `(s, t]`. -/
noncomputable def integral (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  (∫ r in Set.Ioc (s : ℝ) t, h r.toNNReal ω ∂I.posMeasure ω) -
    ∫ r in Set.Ioc (s : ℝ) t, h r.toNNReal ω ∂I.negMeasure ω

/-- The pathwise integral `∫_s^t |h_r| |dA_r|` over `(s, t]`, in `[0, ∞]`. -/
noncomputable def absLIntegral (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc (s : ℝ) t, ‖h r.toNNReal ω‖ₑ ∂I.varMeasure ω

end BVIntegrator

/-- The `L¹(μ)` norm `E(∫_0^T |V_t| |dA_t|) = ∫ |V| dμ` against the Doléans–Dade measure `μ`
of `|A|`, in `[0, ∞]`. -/
noncomputable def L1Norm {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {T β : ℝ≥0} (P : Measure Ω) (I : BVIntegrator 𝓕 T β) (V : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, I.absLIntegral V 0 T ω ∂P

/-- `V ∈ L¹(μ)`: `V` is jointly measurable on `[0,T] × Ω` with finite `L¹(μ)` norm. -/
def MemL1 {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {T β : ℝ≥0} (P : Measure Ω) (I : BVIntegrator 𝓕 T β) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) ∧
    L1Norm P I V < ⊤

/-- `W` is a jointly measurable version of `t ↦ E(ξ_t | 𝓕_t)` on `[0, T]`;
the conditional-expectation arguments are integrable at every time in the horizon. -/
def IsCondExpVersion {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (T : ℝ≥0) (ξ W : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry (fun t ω => if t ≤ T then W t ω else 0)) ∧
    (∀ t ≤ T, Integrable (ξ t) P) ∧
    ∀ t ≤ T, W t =ᵐ[P] MeasureTheory.condExp (𝓕 t) P (ξ t)

end AntonelliBFSDE.Backward
