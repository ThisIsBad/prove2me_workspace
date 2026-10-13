import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {β : ℝ}

/-- The dominating process `D_t = max(|A|_t, |C|_t)` of §3 (p. 785). -/
def Dproc (IA IC : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max (IA.totVar t ω) (IC.totVar t ω)

/-- Every path of `D` is nondecreasing. -/
theorem Dproc_mono (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) : Monotone (fun t => Dproc IA IC t ω) :=
  fun _ _ h => max_le_max
    (add_le_add (IA.mono_pos ω h) (IA.mono_neg ω h))
    (add_le_add (IC.mono_pos ω h) (IC.mono_neg ω h))

/-- The Stieltjes measure `dD(ω)` on `ℝ` of the path `x ↦ D_{x⁺}(ω)`. -/
noncomputable def dD (IA IC : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  (show Monotone (fun x : ℝ => Dproc IA IC x.toNNReal ω) from
    fun _ _ h => Dproc_mono IA IC ω (Real.toNNReal_le_toNNReal h)).stieltjesFunction.measure

/-- The Lebesgue–Stieltjes measure `dc` on `[0, ∞)` of a nondecreasing path `c` with the
convention `c_{0-} = 0` (Dellacherie–Meyer; Remark 2.2, (2.6), p. 780): the Stieltjes measure of
`c` on `(0, ∞)` plus an atom of mass `c_0` at `0`. Every use assumes `c` nondecreasing,
right-continuous and `c_0 ≥ 0`. -/
noncomputable def measureFromZero (c : ℝ≥0 → ℝ) : Measure ℝ :=
  AntonelliBFSDE.Backward.stieltjesMeasureOf c + ENNReal.ofReal (c 0) • Measure.dirac 0

/-- The norm of `L¹(μ)`, `μ` the Doléans measure of `D`:
`‖V‖_{L¹(μ)} = E(∫_0^T |V_t| dD_t)`, the inner integral over `(0, T]`, in `[0, ∞]`. -/
noncomputable def L1NormD (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β)
    (V : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ r in Set.Ioc (0 : ℝ) (T : ℝ), ‖V r.toNNReal ω‖ₑ ∂dD IA IC ω ∂P

/-- `V ∈ L¹(μ)`: `V` is jointly measurable on `ℝ≥0 × Ω` and `E(∫_0^T |V_t| dD_t) < ∞`. -/
def MemL1D (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry V) ∧ L1NormD P IA IC V < ⊤

/-- The pathwise distance `∫_s^t (|U_r - U'_r| + |V_r - V'_r|) dD_r` over `(s, t]`, in `[0, ∞]`. -/
noncomputable def pathDist (IA IC : BVIntegrator 𝓕 T β) (U V U' V' : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc (s : ℝ) (t : ℝ),
    (‖U r.toNNReal ω - U' r.toNNReal ω‖ₑ + ‖V r.toNNReal ω - V' r.toNNReal ω‖ₑ) ∂dD IA IC ω

/-- `‖D‖_{H^∞}`, read as the `P`-essential supremum of the terminal value `D_T`. -/
noncomputable def HInfNorm (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β) : ℝ≥0∞ :=
  essSup (fun ω => ENNReal.ofReal (Dproc IA IC T ω)) P

/-- Domination of `|A|` and `|C|` by `D` on `[0, T]`: `t ↦ D_t - |A|_t` and `t ↦ D_t - |C|_t`
are nondecreasing on `[0, T]` for every `ω`, i.e. `d|A| ≤ dD` and `d|C| ≤ dD` pathwise.
This is the property the paper asserts on p. 786 ("`|A|_t ≪ D_t` and `|C|_t ≪ D_t` with
Radon–Nikodym derivatives ≤ 1"), which does not follow from `D = max(|A|, |C|)`; it is
assumed explicitly. -/
def Dominated (IA IC : BVIntegrator 𝓕 T β) : Prop :=
  (∀ ω, MonotoneOn (fun t => Dproc IA IC t ω - IA.totVar t ω) (Set.Icc 0 T)) ∧
  (∀ ω, MonotoneOn (fun t => Dproc IA IC t ω - IC.totVar t ω) (Set.Icc 0 T))

/-- The standing hypotheses of §3 (p. 785) on the coefficients `f, g`, the constant `k`,
the terminal value `Y` and the forward input `J`:
* `f, g : [0, T] × Ω × ℝ² → ℝ` are jointly measurable;
* (1.) `k > 0` and `f, g` are `k`-Lipschitz in `(x, y)` (sum of absolute differences),
  uniformly in `(s, ω)`, `s ∈ [0, T]`;
* (2.) for every `(x, y)`, `(s, ω) ↦ f_s(ω, x, y)` is progressively measurable, and
  `ω ↦ g_s(ω, x, y)` is `𝓕_s`-measurable for every `s`;
* (3.) `E(∫_0^T |f_s(0, 0)| dD_s) < ∞` and `E(∫_0^T |g_s(0, 0)| dD_s) < ∞`;
* `Y` is `𝓕_T`-measurable and integrable;
* `J` is progressively measurable, jointly measurable, and `E(∫_0^T |J_t| dD_t) < ∞`. -/
structure StandingHyp (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ) : Prop where
  f_meas : Measurable (fun p : ℝ≥0 × Ω × ℝ × ℝ => f p.1 p.2.1 p.2.2.1 p.2.2.2)
  g_meas : Measurable (fun p : ℝ≥0 × Ω × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)
  k_pos : 0 < k
  f_lip : ∀ s ≤ T, ∀ ω x y x' y', |f s ω x y - f s ω x' y'| ≤ k * (|x - x'| + |y - y'|)
  g_lip : ∀ s ≤ T, ∀ ω x y x' y', |g s ω x y - g s ω x' y'| ≤ k * (|x - x'| + |y - y'|)
  f_prog : ∀ x y, IsProgressive 𝓕 (fun s ω => f s ω x y)
  g_adapted : ∀ s x y, Measurable[𝓕 s] (fun ω => g s ω x y)
  f_zero : L1NormD P IA IC (fun s ω => f s ω 0 0) < ⊤
  g_zero : L1NormD P IA IC (fun s ω => g s ω 0 0) < ⊤
  Y_meas : Measurable[𝓕 T] Y
  Y_int : Integrable Y P
  J_prog : IsProgressive 𝓕 J
  J_meas : Measurable (Function.uncurry J)
  J_int : L1NormD P IA IC J < ⊤

/-- The forward component of the operator `Γ` of (3.3):
`F(U, V)_t = J_t + ∫_0^t f_s(U_s, V_s) dA_s`, the integral over `(0, t]`. -/
noncomputable def Fop (IA : BVIntegrator 𝓕 T β) (J : ℝ≥0 → Ω → ℝ)
    (f : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (U V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  J t ω + IA.integral (fun s ω => f s ω (U s ω) (V s ω)) 0 t ω

/-- The random variable inside the conditional expectation of (3.2)/(3.3):
`ξ_t = ∫_t^T g_s(U_s, V_s) dC_s + Y`, the integral over `(t, T]`. -/
noncomputable def xiG (IC : BVIntegrator 𝓕 T β) (g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ)
    (U V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  IC.integral (fun s ω => g s ω (U s ω) (V s ω)) t T ω + Y ω

/-- `W` is a version of the backward component `G(U, V)_t = E(ξ_t | 𝓕_t)` of (3.3) on
`[0, T]`: each `ξ_t` (`t ≤ T`) is integrable, `W` is a jointly measurable version of
`t ↦ E(ξ_t | 𝓕_t)`, and every path of `W` is càdlàg on `[0, T]`. -/
def IsGVersion (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (IC : BVIntegrator 𝓕 T β)
    (g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (U V W : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ≤ T, Integrable (xiG IC g Y U V t) P) ∧
  AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (xiG IC g Y U V) W ∧
  ∀ ω, AntonelliBFSDE.Backward.IsCadlagOn (fun t => W t ω) T

/-- `(U, V)` satisfies the system (3.1)–(3.2) in the `L¹(μ) ⊗ L¹(μ)` sense:
`U, V ∈ L¹(μ)`, `F(U, V)` is jointly measurable, and for some version `W` of `G(U, V)`,
`‖F(U, V) - U‖_{L¹(μ)} + ‖W - V‖_{L¹(μ)} = 0`. -/
def IsSystemSolution (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (IA IC : BVIntegrator 𝓕 T β)
    (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) :
    Prop :=
  MemL1D P IA IC U ∧ MemL1D P IA IC V ∧
  Measurable (Function.uncurry (Fop IA J f U V)) ∧
  ∃ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W ∧
    L1NormD P IA IC (Fop IA J f U V - U) + L1NormD P IA IC (W - V) = 0

end AntonelliBFSDE.BackwardForward
