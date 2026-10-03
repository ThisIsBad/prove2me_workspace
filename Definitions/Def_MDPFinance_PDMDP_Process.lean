import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U]

/-- A **realization of a Markov policy** `π = (f_n)` for a Piecewise Deterministic Markov Decision
Model, started at `x` (Bäuerle–Rieder, p. 245, PDF 256): a probability space carrying the jump
times `T` and post-jump states `Z`, `T_0 = 0`, `Z_0 = x`, `T` strictly increasing to infinity,
such that for all Borel `B` and `t`,
`ℙ^π_x(T_{n+1}-T_n ≤ t, Z_{n+1} ∈ B | T_0,Z_0,…,T_n,Z_n) = λ ∫_0^t e^{-λs} Q(B | φ_s^{f_n(Z_n)}(Z_n),
f_n(Z_n)(s)) ds` — conditioning on the **full history** `(T_0,Z_0,…,T_n,Z_n)`, as in the book. -/
structure PDMDPRealization (Ω : Type*) [MeasurableSpace Ω] (Mk : PDMDPModel E U)
    (f : ℕ → E → ControlFn U) (x : E) where
  ℙrob : Measure Ω
  hprob : IsProbabilityMeasure ℙrob
  T : ℕ → Ω → ℝ
  Z : ℕ → Ω → E
  hT0 : ∀ ω, T 0 ω = 0
  hZ0 : ∀ ω, Z 0 ω = x
  hTmeas : ∀ n, Measurable (T n)
  hZmeas : ∀ n, Measurable (Z n)
  hTmono : ∀ n ω, T n ω < T (n + 1) ω
  hTdiverge : ∀ ω, Tendsto (fun n => T n ω) atTop atTop
  hlaw : ∀ n (B : Set E), MeasurableSet B → ∀ t : ℝ,
    condExp (MeasurableSpace.comap (fun ω => fun k : Fin (n + 1) => (T k ω, Z k ω)) inferInstance)
        ℙrob (Set.indicator {ω | T (n + 1) ω - T n ω ≤ t ∧ Z (n + 1) ω ∈ B} 1)
      =ᵐ[ℙrob] fun ω =>
        Mk.lam * ∫ s in Set.Ioc (0 : ℝ) t, Real.exp (-Mk.lam * s) *
          (Mk.Q (Mk.φ s (f n (Z n ω)).1 (Z n ω), (f n (Z n ω)).1 s) B).toReal

variable {Ω : Type*} [MeasurableSpace Ω] {Mk : PDMDPModel E U} {f : ℕ → E → ControlFn U} {x : E}

/-- The step `n` such that `t ∈ [T_n(ω), T_{n+1}(ω))`; `0` as a junk value when `t < 0`. -/
noncomputable def PDMDPRealization.jumpIndex (R : PDMDPRealization Ω Mk f x) (ω : Ω) (t : ℝ) :
    ℕ :=
  if h : ∃ n, R.T n ω ≤ t ∧ t < R.T (n + 1) ω then h.choose else 0

/-- The piecewise deterministic path `X_t = φ^{f_n(Z_n)}_{t-T_n}(Z_n)` for `t ∈ [T_n,T_{n+1})`
(Bäuerle–Rieder, p. 245, PDF 256). -/
noncomputable def PDMDPRealization.X (R : PDMDPRealization Ω Mk f x) (ω : Ω) (t : ℝ) : E :=
  Mk.φ (t - R.T (R.jumpIndex ω t) ω) (f (R.jumpIndex ω t) (R.Z (R.jumpIndex ω t) ω)).1
    (R.Z (R.jumpIndex ω t) ω)

/-- The control process `π_t = f_n(Z_n)(t-T_n)` for `t ∈ [T_n,T_{n+1})` (Bäuerle–Rieder, p. 245,
PDF 256). -/
noncomputable def PDMDPRealization.piCtrl (R : PDMDPRealization Ω Mk f x) (ω : Ω) (t : ℝ) : U :=
  (f (R.jumpIndex ω t) (R.Z (R.jumpIndex ω t) ω)).1 (t - R.T (R.jumpIndex ω t) ω)

/-- `V^π(x) := 𝔼^π_x[∫_0^∞ e^{-βt} r(X_t,π_t) dt] ∈ [-∞,∞]` (Bäuerle–Rieder, Eq. (8.2), p. 245,
PDF 256), well defined under the Integrability Assumption (A). -/
noncomputable def PDMDPRealization.Vpi (R : PDMDPRealization Ω Mk f x) : EReal :=
  erealIntegral R.ℙrob fun ω =>
    erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
      ((Real.exp (-Mk.β * t) * Mk.r (R.X ω t, R.piCtrl ω t) : ℝ) : EReal)

/-- A Markov policy `(f_n)` of the embedded model: measurable decision rules `f_n : E → A`. -/
def IsPDPolicy (f : ℕ → E → ControlFn U) : Prop := ∀ n, Measurable (f n)

/-- The `n`-stage reward-to-go of the **embedded discrete-time model** `(E,A,Q',r'_{rew})` under a
reward rate `rew` (Bäuerle–Rieder, p. 247-248, PDF 258-259): `J_n(f)(x) = r'(x,f_0(x)) + ∫
J_{n-1}(f∘shift) dQ'(·|x,f_0(x))`, `J_0 ≡ 0`, in `[-∞,∞]`. -/
noncomputable def JnEmbedWith (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (rew : E × U → ℝ)
    (f : ℕ → E → ControlFn U) : ℕ → E → EReal
  | 0, _ => 0
  | (n + 1), x =>
      Mk.rprimeWith rew (x, f 0 x) +
        erealIntegral (Emb.Qprime (x, f 0 x)) (JnEmbedWith Mk Emb rew (fun k => f (k + 1)) n)

/-- `J_n(f)` for the reward `r`. -/
noncomputable def JnEmbed (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk)
    (f : ℕ → E → ControlFn U) : ℕ → E → EReal :=
  JnEmbedWith Mk Emb Mk.r f

/-- `J_∞(f)(x) = lim_n J_n(f)(x)` (Bäuerle–Rieder, p. 248, PDF 259), as a `limsup`. -/
noncomputable def JinfEmbed (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk)
    (f : ℕ → E → ControlFn U) (x : E) : EReal :=
  atTop.limsup fun n => JnEmbed Mk Emb f n x

/-- `J_∞(x) := sup_{(f_n)} J_∞(f_n)(x)` over Markov policies of the embedded model with
**nonrelaxed** controls (Bäuerle–Rieder, p. 248, PDF 259). -/
noncomputable def JinfSup (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (x : E) : EReal :=
  ⨆ f ∈ {f : ℕ → E → ControlFn U | IsPDPolicy f}, JinfEmbed Mk Emb f x

/-- The Integrability Assumption (A) (Bäuerle–Rieder, p. 245, PDF 256), through the embedding:
`sup_π 𝔼^π_x[∫_0^∞ e^{-βt} r⁺(X_t,π_t) dt] < ∞` for all `x`. -/
def IntegrabilityAssumptionPD (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) : Prop :=
  ∀ x : E, (⨆ f ∈ {f : ℕ → E → ControlFn U | IsPDPolicy f},
    atTop.limsup fun n => JnEmbedWith Mk Emb (fun p => max (Mk.r p) 0) f n x) < ⊤

/-- `(Lv)(x,α) := r'(x,α) + ∫ v dQ'(·|x,α)` (Bäuerle–Rieder, p. 248, PDF 259). -/
noncomputable def LEmbed (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (v : E → EReal)
    (xα : E × ControlFn U) : EReal :=
  Mk.rprime xα + erealIntegral (Emb.Qprime xα) v

/-- `(Tv)(x) := sup_{α ∈ A} (Lv)(x,α)` (Bäuerle–Rieder, p. 248, PDF 259). -/
noncomputable def TEmbed (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (v : E → EReal) (x : E) :
    EReal :=
  ⨆ α : ControlFn U, LEmbed Mk Emb v (x, α)

end MDPFinance.PDMDP
