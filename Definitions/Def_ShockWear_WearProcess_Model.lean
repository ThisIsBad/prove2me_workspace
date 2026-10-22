import Mathlib

namespace ShockWear.WearProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The Poisson weight e^{−λt}(λt)^k/k!. -/
noncomputable def poisW (lam t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(lam * t)) * (lam * t) ^ k / (k.factorial : ℝ)

/-- (2.1): H̄(t) = Σ_k P̄_k e^{−λt}(λt)^k/k! for t ≥ 0, and H̄(t) = 1 for t < 0. -/
noncomputable def shockSurv (lam : ℝ) (P : ℕ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then 1 else ∑' k, P k * poisW lam t k

/-- Ageing class (iv), p. 631: increasing hazard rate average (IHRA),
`[F̄(t)]^{1/t}` is decreasing in `t > 0` (real power). -/
def IsIHRA (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => Fb t ^ (1 / t)) (Set.Ioi 0)

/-- `Z_k = X_1 + ⋯ + X_k`; the Lean `X i` is the paper's `X_{i+1}`, so `psum X k` is the
paper's `Z_k` and `psum X 0 = 0` is `Z_0 = 0`. -/
def psum {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, X i ω

/-- Conditions (4.3), (4.4), (4.5) of p. 636 for nonnegative damages `X` on `(Ω, pr)`, with
`κ k` a version of the conditional law of the paper's `X_{k+1}` given `Z_k`:

* (4.3) the conditional law of `X_{k+1}` given `(X_1, …, X_k)` is, `pr`-a.e., `κ k` evaluated at
  `Z_k = X_1 + ⋯ + X_k`;
* (4.4) `P{X_{k+1} ≤ u | Z_k = z} = κ k z (−∞, u]` is decreasing in `z ≥ 0`;
* (4.5) `P{X_{k+1} ≤ u | Z_k = z} ≥ P{X_{k+2} ≤ u | Z_{k+1} = z}` for `z ≥ 0`. -/
structure IsDamageSeq {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsFiniteMeasure pr]
    (X : ℕ → Ω → ℝ) (κ : ℕ → Kernel ℝ ℝ) : Prop where
  meas : ∀ i, Measurable (X i)
  nonneg : ∀ i, ∀ᵐ ω ∂pr, 0 ≤ X i ω
  markov : ∀ k, IsMarkovKernel (κ k)
  cond : ∀ k, condDistrib (X k) (fun ω (i : Fin k) => X i ω) pr
           =ᵐ[pr.map (fun ω (i : Fin k) => X i ω)] fun v => κ k (∑ i, v i)
  dec_z : ∀ k u, AntitoneOn (fun z => κ k z (Set.Iic u)) (Set.Ici 0)
  dec_k : ∀ k u z, 0 ≤ z → κ (k + 1) z (Set.Iic u) ≤ κ k z (Set.Iic u)

set_option warn.classDefReducibility false in
/-- The natural filtration at time `s`: `σ(Z(r), r ≤ s)`. -/
def natFilt {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (r : ℝ≥0) (_ : r ≤ s), MeasurableSpace.comap (Z r) inferInstance

/-- Condition (4.8), p. 640, read pathwise: every `Z(t)` is a random variable, and almost every
sample path starts at `0` and is nondecreasing. -/
structure IsMonotoneWear {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) : Prop where
  meas : ∀ t, Measurable (Z t)
  start_mono : ∀ᵐ ω ∂pr, Z 0 ω = 0 ∧ Monotone (fun t => Z t ω)

/-- Conditions (4.8), (4.9), (4.10), pp. 640–641, with `κ t Δ` a version of the conditional law of
the increment `Z(t + Δ) − Z(t)` given `Z(t)`:

* (4.8) `IsMonotoneWear pr Z`;
* (4.9) `{Z(t)}` is a Markov process for its natural filtration: for `s ≤ t` and Borel `B`,
  `P{Z(t) ∈ B | Z(r), r ≤ s} = P{Z(t) ∈ B | Z(s)}` a.s.;
* (4.10) `P{Z(t + Δ) − Z(t) ≤ u | Z(t) = z} = κ t Δ z (−∞, u]` is decreasing in both `z` and `t`
  in the region `t ≥ 0`, `z ≥ 0`, `Δ ≥ 0`. -/
structure IsWearProcess {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsFiniteMeasure pr]
    (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ) : Prop extends IsMonotoneWear pr Z where
  markov : ∀ s t : ℝ≥0, s ≤ t → ∀ B : Set ℝ, MeasurableSet B →
    pr[(Z t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | natFilt Z s] =ᵐ[pr]
      pr[(Z t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap (Z s) inferInstance]
  kernel_markov : ∀ t Δ, IsMarkovKernel (κ t Δ)
  incr_law : ∀ t Δ, condDistrib (fun ω => Z (t + Δ) ω - Z t ω) (Z t) pr
    =ᵐ[pr.map (Z t)] κ t Δ
  dec : ∀ (Δ : ℝ≥0) (u : ℝ) (t t' : ℝ≥0) (z z' : ℝ), t ≤ t' → 0 ≤ z → z ≤ z' →
    κ t' Δ z' (Set.Iic u) ≤ κ t Δ z (Set.Iic u)

/-- The first passage time `T_x = inf {t : Z(t) > x}`, in `[0, ∞]` (`∞` if the level is never
exceeded). -/
noncomputable def passTime {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (x : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : x < Z t ω), (t : ℝ≥0∞)

/-- The survival function of `T_x`: `H̄_x(t) = P{T_x > t}` for `t ≥ 0`, and `= 1` for `t < 0`. -/
noncomputable def passSurv {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (x t : ℝ) : ℝ :=
  if t < 0 then 1 else (pr {ω | ENNReal.ofReal t < passTime Z x ω}).toReal

/-- The distribution function of the wear at time `t`: `F_t(x) = P{Z(t) ≤ x}`. -/
noncomputable def wearCdf {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  (pr {ω | Z t ω ≤ x}).toReal

/-- The increments `X_i = Z(iΔ) − Z((i − 1)Δ)` of the proof of Theorem 4.10; the Lean `wearIncr Z Δ i`
is the paper's `X_{i+1} = Z((i + 1)Δ) − Z(iΔ)`. -/
def wearIncr {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (Δ : ℝ≥0) (i : ℕ) (ω : Ω) : ℝ :=
  Z ((i + 1 : ℕ) • Δ) ω - Z (i • Δ) ω

end ShockWear.WearProcess
