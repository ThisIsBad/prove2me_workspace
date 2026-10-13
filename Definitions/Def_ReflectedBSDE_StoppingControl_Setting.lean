import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_Existence_Setting

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- §2, p. 703: the natural filtration of the Brownian motion `B`, augmented so that `𝓕₀`
(hence every `𝓕_t`) contains all `P`-null sets of `𝓕`:
`𝓕_t = σ{B_s ; s ≤ t} ∨ σ{N ∈ 𝓕 : P(N) = 0}`. -/
noncomputable def augFiltration {d : ℕ} {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ}
    (hB : Peng1990.SMP.IsStdBrownian P B) : Filtration ℝ≥0 mΩ where
  seq t := Peng1990.SMP.brownianFiltration hB t ⊔ ReflectedBSDE.Existence.nullSigma P
  mono' _ _ hst := sup_le_sup_right ((Peng1990.SMP.brownianFiltration hB).mono hst) _
  le' t := sup_le ((Peng1990.SMP.brownianFiltration hB).le t)
    (MeasurableSpace.generateFrom_le fun _ hs => hs.1)

/-- The Euclidean norm `|z| = (Σⱼ zⱼ²)^{1/2}` on `ℝ^d`. -/
noncomputable def eucNorm {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ j, z j ^ 2)

/-- The Euclidean inner product `⟨γ, z⟩ = Σⱼ γⱼ zⱼ` on `ℝ^d`. -/
def dot {d : ℕ} (γ z : Fin d → ℝ) : ℝ :=
  ∑ j, γ j * z j

/-- `𝕃²`: `ξ` is `𝓕_T`-measurable and `E|ξ|² < ∞`. -/
def IsTerminalL2 (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (ξ : Ω → ℝ) : Prop :=
  StronglyMeasurable[𝓕 T] ξ ∧ MemLp ξ 2 P

/-- `𝒮²`: `φ` is progressively measurable (in place of predictable) and
`E(sup_{0 ≤ t ≤ T} |φ_t|²) < ∞`, the expectation computed in `ℝ≥0∞`. -/
def InS2 (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 φ ∧ ∫⁻ ω, (⨆ t ∈ Set.Iic T, ‖φ t ω‖ₑ ^ 2) ∂P < ⊤

/-- §2, pp. 703–704: the data `(ξ, f, S)` satisfy (i), (ii) and (iv), and `S_T ≤ ξ` a.s.
(the Lipschitz condition (iii) is the separate predicate `IsLipschitzCoeff`).
* (i) `ξ ∈ 𝕃²`;
* (ii) for every `(y, z)`, the process `f(·, y, z)` lies in `ℍ²` (progressive, `E∫₀ᵀ|f|² < ∞`);
* (iv) `S` is a continuous (on `[0, T]`, every path) progressively measurable real process with
  `E(sup_{0 ≤ t ≤ T} (S_t⁺)²) < ∞`;
* `S_T ≤ ξ` a.s. ("We shall always assume", p. 704). -/
structure StandingData {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ) : Prop where
  terminal : IsTerminalL2 𝓕 P T ξ
  coeff_mem : ∀ (y : ℝ) (z : Fin d → ℝ), Peng1990.SMP.L2F 𝓕 P T (fun t ω => f t ω y z)
  obstacle_cont : ∀ ω, ContinuousOn (fun t => S t ω) (Set.Iic T)
  obstacle_prog : IsStronglyProgressive 𝓕 S
  obstacle_sq : ∫⁻ ω, (⨆ t ∈ Set.Iic T, ENNReal.ofReal (max (S t ω) 0) ^ 2) ∂P < ⊤
  obstacle_le_terminal : ∀ᵐ ω ∂P, S T ω ≤ ξ ω

/-- §2, (iii), p. 704: `f` is Lipschitz in `(y, z)` with constant `K > 0`, uniformly in `t`,
almost surely: for a.e. `ω`, for all `t ∈ [0, T]` and all `y, y', z, z'`,
`|f(t, y, z) − f(t, y', z')| ≤ K(|y − y'| + |z − z'|)` (Euclidean `|·|` on `ℝ^d`). -/
def IsLipschitzCoeff {d : ℕ} (P : Measure Ω) (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (K : ℝ) : Prop :=
  0 < K ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, ∀ (y y' : ℝ) (z z' : Fin d → ℝ),
    |f t ω y z - f t ω y' z'| ≤ K * (|y - y'| + eucNorm (z - z'))

/-- The path `s ↦ K_{(s ∧ T)⁺}(ω)` of a process on `[0, T]`, extended to all of `ℝ` by `K_0`
on `(-∞, 0]` and by `K_T` on `[T, ∞)`. -/
noncomputable def pathExt (K : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ → ℝ :=
  fun s => K (min s (T : ℝ)).toNNReal ω

/-- §2, (v)–(viii), p. 704: `(Y, Z, K)` is a square-integrable solution of the reflected BSDE
with terminal value `ξ`, coefficient `f` and obstacle `S`, driven by the `d`-dimensional
Brownian motion `B`:
* `Y`, `Z`, `K` are `𝓕`-progressively measurable, valued in `ℝ`, `ℝ^d`, `ℝ` (`K ≥ 0` follows
  from `K₀ = 0` and monotonicity);
* (v) `Z ∈ ℍ²`; (v′) `Y ∈ 𝒮²` and `K_T ∈ 𝕃²`;
* `Y` has continuous paths on `[0, T]` (p. 704: this follows from (vi) and (viii));
* (vi) for some Itô integral processes `Jⱼ = ∫₀^· Z^j dB^j`, for every `t ∈ [0, T]`, a.s.,
  `Y_t = ξ + ∫ₜᵀ f(s, Y_s, Z_s) ds + K_T − K_t − Σⱼ (Jⱼ(T) − Jⱼ(t))`;
* (vii) a.s., `Y_t ≥ S_t` for all `t ∈ [0, T]`;
* (viii) every path of `K` is continuous and nondecreasing with `K₀ = 0`, and a.s.
  `∫₀ᵀ (Y_t − S_t) dK_t = 0`, the integral taken against the Lebesgue–Stieltjes measure of the
  path of `K` (a lower Lebesgue integral of the nonnegative integrand). -/
structure IsRBSDESolution {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ) :
    Prop where
  progY : IsStronglyProgressive 𝓕 Y
  progZ : IsStronglyProgressive 𝓕 Z
  progK : IsStronglyProgressive 𝓕 K
  Z_mem : Peng1990.SMP.L2F 𝓕 P T Z
  Y_mem : InS2 𝓕 P T Y
  K_mem : MemLp (K T) 2 P
  Y_cont : ∀ ω, ContinuousOn (fun t => Y t ω) (Set.Iic T)
  eqn : ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
    (∀ j, Peng1990.SMP.IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => Z s ω j) (J j)) ∧
    ∀ t ≤ T, ∀ᵐ ω ∂P,
      IntegrableOn (fun s : ℝ => f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
        (Set.Icc (t : ℝ) T) ∧
      Y t ω = ξ ω + (∫ s in Set.Icc (t : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
        + K T ω - K t ω - ∑ j, (J j T ω - J j t ω)
  above : ∀ᵐ ω ∂P, ∀ t ≤ T, S t ω ≤ Y t ω
  K_mono : ∀ ω, Monotone (pathExt K T ω)
  K_cont : ∀ ω, Continuous (pathExt K T ω)
  K_zero : ∀ ω, K 0 ω = 0
  skorokhod : ∀ᵐ ω ∂P,
    ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Y s.toNNReal ω - S s.toNNReal ω)
      ∂(K_mono ω).stieltjesFunction.measure = 0

/-- `𝒯_t`: the `𝓕`-stopping times `v` with `t ≤ v ≤ T` (real valued, so never `∞`). -/
def stoppingTimesFrom (𝓕 : Filtration ℝ≥0 mΩ) (T t : ℝ≥0) : Set (Ω → ℝ≥0) :=
  {v | IsStoppingTime 𝓕 (fun ω => ((v ω : ℝ≥0) : WithTop ℝ≥0)) ∧ ∀ ω, t ≤ v ω ∧ v ω ≤ T}

/-- `g` is an essential supremum of the family `𝒳` of real random variables, relative to the
sub-σ-algebra `m'` and the measure `μ`: `g` is `m'`-measurable, `X ≤ g` a.e. for every
`X ∈ 𝒳`, and `g ≤ g'` a.e. for every `m'`-measurable `g'` with `X ≤ g'` a.e. for all `X ∈ 𝒳`.
(The mirror image of the published `MultiperiodRisk.Bellman.IsEssInf`.) -/
def IsEssSup (μ : Measure Ω) (m' : MeasurableSpace Ω) (𝒳 : Set (Ω → ℝ)) (g : Ω → ℝ) : Prop :=
  StronglyMeasurable[m'] g ∧ (∀ X ∈ 𝒳, X ≤ᵐ[μ] g) ∧
    ∀ g' : Ω → ℝ, StronglyMeasurable[m'] g' → (∀ X ∈ 𝒳, X ≤ᵐ[μ] g') → g ≤ᵐ[μ] g'

end ReflectedBSDE.StoppingControl
