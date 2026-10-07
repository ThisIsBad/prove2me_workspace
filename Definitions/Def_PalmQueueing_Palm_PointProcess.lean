import Mathlib

/-!
# Stationary marked point processes and Palm probability (§§1.1-1.2, pp.2-20)

The vocabulary chapter 1 builds before its first numbered result, and which the rest of the book
uses without restating: the points of a simple point process on `ℝ` with the convention
`T₀ ≤ 0 < T₁`, a measurable flow `{θ_t}`, compatibility of a process and of a point process with
that flow, marks, the intensity `λ`, and Palm probability `P⁰_N` by the Matthes definition in
terms of counting (Eq. (1.2.1), p.14).

Palm probability is introduced as a **predicate** characterising `P⁰_N` by the book's own defining
identity, not as a measure built to satisfy Mecke's formula. That is deliberate: Mecke's formula
(1.2.17) and the inversion formula (1.2.25) are then statements with content rather than
restatements of a definition.
-/

namespace PalmQueueing.Palm

open MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable flow `{θ_t}` on `(Ω, F)` (pp.4-5): a one-parameter group of maps such that
`(t, ω) ↦ θ_t ω` is measurable from `B ⊗ F` to `F` (p.5, (a)). The joint measurability is what
makes `ω ↦ ∫ f(θ_t ω) dt` and `ω ↦ f(θ_{T_n(ω)} ω)` random variables. -/
structure Flow (Ω : Type*) [MeasurableSpace Ω] where
  /-- The shift `θ_t`. -/
  toFun : ℝ → Ω → Ω
  /-- `(t, ω) ↦ θ_t ω` is jointly measurable (p.5, (a)). -/
  measurable_uncurry : Measurable fun p : ℝ × Ω => toFun p.1 p.2
  /-- Each shift is measurable. -/
  measurable' : ∀ t, Measurable (toFun t)
  /-- `θ₀` is the identity. -/
  map_zero : toFun 0 = id
  /-- `θ_{s+t} = θ_s ∘ θ_t`. -/
  map_add : ∀ s t, toFun (s + t) = toFun s ∘ toFun t

/-- `θ_t ω`, written as application. -/
instance : CoeFun (Flow Ω) (fun _ => ℝ → Ω → Ω) := ⟨Flow.toFun⟩

/-- `P` is `θ_t`-invariant: the point process is **stationary** (p.3). -/
def Flow.Invariant (θ : Flow Ω) (P : Measure Ω) : Prop :=
  ∀ t : ℝ, Measure.map (θ t) P = P

/-- `(P, {θ_t})` is **ergodic** (p.76): `P` is `θ_t`-invariant, and every `θ_t`-invariant event is
`P`-null or `P`-almost sure. Stated here rather than in any one chapter's module because four of
the five missions of this series need it and two private copies would silently drift apart. -/
def IsErgodicFlow (θ : Flow Ω) (P : Measure Ω) : Prop :=
  θ.Invariant P ∧
    ∀ B : Set Ω, MeasurableSet B → (∀ t : ℝ, θ t ⁻¹' B = B) → P B = 0 ∨ P B = 1

/-- A simple point process on `ℝ`, carried by its points `{T_n}_{n ∈ ℤ}` (§1.1.1, p.2).

The indexing convention `T₀ ≤ 0 < T₁` is the book's and is not optional: every inversion-formula
statement depends on `T₀` being the last point at or before the origin. -/
structure PointProcess (Ω : Type*) [MeasurableSpace Ω] where
  /-- The `n`-th point. -/
  T : ℤ → Ω → ℝ
  /-- Each point is a random variable. -/
  measurable_T : ∀ n, Measurable (T n)
  /-- The points are strictly increasing: the process is simple. -/
  strictMono : ∀ ω, StrictMono fun n => T n ω
  /-- `T₀ ≤ 0`. -/
  zero_le : ∀ ω, T 0 ω ≤ 0
  /-- `0 < T₁`. -/
  lt_one : ∀ ω, (0 : ℝ) < T 1 ω
  /-- The points have no accumulation at `+∞`: local finiteness to the right. -/
  tendsto_atTop : ∀ ω, Tendsto (fun n => T n ω) atTop atTop
  /-- The points have no accumulation at `-∞`: local finiteness to the left. -/
  tendsto_atBot : ∀ ω, Tendsto (fun n => T n ω) atBot atBot

/-- The counting measure `N(ω, ·)` of the point process, `N(ω, C) = #{n : T_n(ω) ∈ C}`. -/
noncomputable def PointProcess.count (N : PointProcess Ω) (ω : Ω) : Measure ℝ :=
  Measure.sum fun n : ℤ => Measure.dirac (N.T n ω)

/-- A stochastic process `{Z(t)}` with values in `E` is **`θ_t`-compatible** (p.3):
`Z(t, θ_s ω) = Z(t + s, ω)`. -/
def IsCompatible {E : Type*} (θ : Flow Ω) (Z : ℝ → Ω → E) : Prop :=
  ∀ (t s : ℝ) (ω : Ω), Z t (θ s ω) = Z (t + s) ω

/-- A point process is **compatible with the flow** (p.3): `N(θ_t ω, C) = N(ω, C + t)`.

Equivalently, and this is the form used below, the points shift: `T_n(θ_t ω) = T_n(ω) - t` after
the reindexing that restores `T₀ ≤ 0 < T₁`. The measure form is stated because it is the one the
book's formulas integrate against. -/
def PointProcess.Compatible (N : PointProcess Ω) (θ : Flow Ω) : Prop :=
  ∀ (t : ℝ) (ω : Ω) (C : Set ℝ), MeasurableSet C →
    N.count (θ t ω) C = N.count ω ((fun s => s - t) ⁻¹' C)

/-- `{Zl(t)}` is the **left-limit process** of `{Z(t)}`: `Zl(s) = Z(s-)`. Carried as a separate
process with this property rather than constructed, because nothing in the book's hypotheses forces
a process to be regularisable by a formula. -/
def IsLeftLimitProcess (Z Zl : ℝ → Ω → ℝ) : Prop :=
  ∀ (s : ℝ) (ω : Ω), Filter.Tendsto (fun u => Z u ω) (nhdsWithin s (Set.Iio s)) (nhds (Zl s ω))

/-- A sequence of **marks** of `(N, θ_t)` with values in `(K, 𝒦)` (§1.1.3, p.6): random variables
`Z_n` attached to the points, shifting with the flow as `Z_n(θ_{T_k} ω) = Z_{n+k}(ω)`. -/
def IsMarkSequence {K : Type*} [MeasurableSpace K] (θ : Flow Ω) (N : PointProcess Ω)
    (Z : ℤ → Ω → K) : Prop :=
  (∀ n, Measurable (Z n)) ∧ ∀ (n k : ℤ) (ω : Ω), Z n (θ (N.T k ω) ω) = Z (n + k) ω

/-- The **intensity** `λ` of a stationary point process (§1.1.5, p.12):
`λ = E[N((0, 1])]`. -/
def IsIntensity (N : PointProcess Ω) (P : Measure Ω) (lam : ℝ) : Prop :=
  0 < lam ∧ ENNReal.ofReal lam = ∫⁻ ω, N.count ω (Set.Ioc (0 : ℝ) 1) ∂P

/-- The **Campbell measure** of `(N, P)` (§1.1.6, p.13): the measure on `Ω × ℝ` given by
`C(A × B) = E[ 1_A · N(B) ]`, here as the value it takes on a rectangle. -/
noncomputable def campbell (N : PointProcess Ω) (P : Measure Ω) (A : Set Ω) (B : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, Set.indicator A (fun _ => (1 : ℝ≥0∞)) ω * N.count ω B ∂P

/-- **Palm probability**, by the Matthes definition in terms of counting (§1.2.1, p.14).

`P⁰_N` is the probability for which the defining formula (1.2.1) holds: for every `t > 0` and
every measurable `A`,

`λ t P⁰_N(A) = E[ Σ_{n ∈ ℤ} 1_A(θ_{T_n}) 1_{(0,t]}(T_n) ]`.

Carried as a predicate rather than as a construction so that Mecke's formula and the inversion
formula remain theorems. -/
def IsPalmProbability (θ : Flow Ω) (N : PointProcess Ω) (P P0 : Measure Ω) (lam : ℝ) : Prop :=
  IsProbabilityMeasure P0 ∧
  ∀ A : Set Ω, MeasurableSet A → ∀ t : ℝ, 0 < t →
    ENNReal.ofReal (lam * t) * P0 A =
      ∫⁻ ω, ∑' n : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (N.T n ω) *
        Set.indicator A (fun _ => (1 : ℝ≥0∞)) (θ (N.T n ω) ω) ∂P

/-- The standing hypotheses of chapter 1: a stationary simple point process on `(Ω, F, P)`,
compatible with a measurable flow, with finite non-null intensity, together with its Palm
probability. -/
structure PalmSetting (Ω : Type*) [MeasurableSpace Ω] where
  /-- The flow. -/
  θ : Flow Ω
  /-- The point process. -/
  N : PointProcess Ω
  /-- The stationary probability. -/
  P : Measure Ω
  /-- The Palm probability. -/
  P0 : Measure Ω
  /-- The intensity. -/
  lam : ℝ
  /-- `P` is a probability. -/
  isProb : IsProbabilityMeasure P
  /-- `P` is `θ_t`-invariant. -/
  invariant : θ.Invariant P
  /-- `N` is compatible with the flow. -/
  compatible : N.Compatible θ
  /-- `λ` is the intensity of `N`. -/
  intensity : IsIntensity N P lam
  /-- `P⁰_N` is the Palm probability. -/
  palm : IsPalmProbability θ N P P0 lam

end PalmQueueing.Palm
