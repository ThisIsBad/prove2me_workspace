import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Hypotheses 1–4 of §2 (Antonelli 1993, pp. 778–779) on the driver `g` and the terminal
value `Y` of the backward equation (2.1), for the integrator `I` on `[0, T]`. -/
structure Hypotheses {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (k : ℝ) : Prop where
  /-- `g` is `𝓑 × 𝓕 × 𝓑(ℝ) / 𝓑(ℝ)`-measurable. -/
  measurable : Measurable fun p : ℝ≥0 × Ω × ℝ => g p.1 p.2.1 p.2.2
  /-- 1. the Lipschitz constant is positive. -/
  k_pos : 0 < k
  /-- 1., (2.2): `g` is uniformly Lipschitz in `u`, uniformly in `s ∈ [0, T]` and `ω`. -/
  lipschitz : ∀ s ≤ T, ∀ ω u v, |g s ω u - g s ω v| ≤ k * |u - v|
  /-- 2. `g_s(·, u)` is `𝓕_s`-measurable for each `s ∈ [0, T]` and `u`. -/
  adapted : ∀ s ≤ T, ∀ u, Measurable[𝓕 s] fun ω => g s ω u
  /-- 3. `E(∫_0^T |g_s(0)| |dA_s|) < +∞`. -/
  integrable_zero : L1Norm P I (fun s ω => g s ω 0) < ⊤
  /-- 4. `Y ∈ L¹(P)`. -/
  integrable_Y : Integrable Y P
  /-- 4. `Y` is `𝓕_T`-measurable. -/
  measurable_Y : Measurable[𝓕 T] Y

/-- The argument of the conditional expectation in (2.1):
`ξ_t = ∫_t^T g_s(V_s) dA_s + Y`, the integral being over `(t, T]`. -/
noncomputable def xi {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  I.integral (fun s ω => g s ω (V s ω)) t T ω + Y ω

/-- `W` is a version of `G(V)` of (2.1): every `ξ_t` (`t ≤ T`) is integrable, `W` is a
jointly measurable version of `t ↦ E(ξ_t | 𝓕_t)`, and every path of `W` is càdlàg on `[0, T]`
(the paper works with càdlàg processes throughout, after Protter 1990). Two càdlàg versions are
indistinguishable on `[0, T]`; mere jointly measurable versions could differ on the graph of a
random time charged by `|dA|`, a set of positive `μ`-measure. -/
def IsGVersion {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (V W : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ≤ T, Integrable (xi I g Y V t) P) ∧ IsCondExpVersion 𝓕 P T (xi I g Y V) W ∧
    ∀ ω, IsCadlagOn (fun t => W t ω) T

/-- `V` solves (2.1) in the `L¹(μ)` sense: `V ∈ L¹(μ)` and `E(∫_0^T |G(V)_t - V_t| |dA_t|) = 0`
for a càdlàg version `G(V)` (any two càdlàg versions are indistinguishable on `[0, T]`). -/
def IsL1Solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) {T β : ℝ≥0} (I : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ)
    (V : ℝ≥0 → Ω → ℝ) : Prop :=
  MemL1 P I V ∧ ∃ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P I g Y V W ∧
    ∫⁻ ω, I.absLIntegral (fun s ω => W s ω - V s ω) 0 T ω ∂P = 0

/-- The Lebesgue–Stieltjes measure `dc` on `[0, ∞)` of a nondecreasing path `c` with the
convention `c_{0-} = 0` (Dellacherie–Meyer; Antonelli 1993, (2.6), p. 780): the Stieltjes measure
of `c` on `(0, ∞)` plus an atom of mass `c_0` at `0`. Every use assumes `c` nondecreasing,
right-continuous and `c_0 ≥ 0`. -/
noncomputable def measureFromZero (c : ℝ≥0 → ℝ) : Measure ℝ :=
  stieltjesMeasureOf c + ENNReal.ofReal (c 0) • Measure.dirac 0

/-- The iterated Stieltjes integrals `a^{(n)}` of a path `a` (proof of Theorem 2.4, p. 780):
`a^{(0)} = 1` and `a^{(n+1)}_t = ∫_{(0,t]} a^{(n)}_s da_s`. -/
noncomputable def iterInt (a : ℝ≥0 → ℝ) : ℕ → ℝ≥0 → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ s in Set.Ioc (0 : ℝ) t, iterInt a n s.toNNReal ∂stieltjesMeasureOf a

/-- The iterated Stieltjes integrals `a^{(n-)}` with left limits (p. 780):
`a^{(0-)} = 1` and `a^{((n+1)-)}_t = ∫_{(0,t]} a^{(n-)}_{s-} da_s`. -/
noncomputable def iterIntMinus (a : ℝ≥0 → ℝ) : ℕ → ℝ≥0 → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun t =>
      ∫ s in Set.Ioc (0 : ℝ) t, Function.leftLim (iterIntMinus a n) s.toNNReal
        ∂stieltjesMeasureOf a

/-- `(a_u - a_t)^{[n]} = ∑_{i=0}^n (-1)^i a_u^{((n-i)-)} a_t^{(i)}` (p. 780). -/
noncomputable def bracket (a : ℝ≥0 → ℝ) (n : ℕ) (u t : ℝ≥0) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * iterIntMinus a (n - i) u * iterInt a i t

/-- `(a_{u-} - a_t)^{[n]} = ∑_{i=0}^n (-1)^i a_{u-}^{((n-i)-)} a_t^{(i)}`, the same formula with
left limits in `u` (p. 780, "the same formula holding also for `u_-`"). -/
noncomputable def bracketLeft (a : ℝ≥0 → ℝ) (n : ℕ) (u t : ℝ≥0) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ i * Function.leftLim (iterIntMinus a (n - i)) u * iterInt a i t

end AntonelliBFSDE.Backward
