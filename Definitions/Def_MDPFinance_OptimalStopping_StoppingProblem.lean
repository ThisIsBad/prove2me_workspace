import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.OptimalStopping

/-- The `[-∞,∞]`-valued integral `∫ v⁺ − ∫ v⁻` of an extended-real function (with `∞ − ∞ = −∞`
by EReal's `⊤ + ⊥ = ⊥`): expectations of rewards whose positive part is integrable are genuine
values in `[-∞,∞)`, never a real integral that silently returns `0`. -/
noncomputable def erealIntegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    EReal :=
  ((∫⁻ a, (v a ⊔ 0).toENNReal ∂μ : ℝ≥0∞) : EReal) + (-((∫⁻ a, ((-v a) ⊔ 0).toENNReal ∂μ : ℝ≥0∞) : EReal))

/-- The data of a **stopping problem with finite horizon `N`** (§10.1, p. 304, in the
substochastic Markov Decision Model formulation of p. 305): an uncontrolled Markov process on
`E` with transition kernels `Q^X_n`, a running reward `c_n` collected while continuing, and a
stopping reward `g_n`, with `g_N` the terminal reward. -/
structure StoppingProblem (E : Type*) [MeasurableSpace E] (N : ℕ) where
  QX : ℕ → E → Measure E
  QX_prob : ∀ n x, IsProbabilityMeasure (QX n x)
  QX_meas : ∀ n, Measurable (QX n)
  c : ℕ → E → ℝ
  c_meas : ∀ n, Measurable (c n)
  g : ℕ → E → ℝ
  g_meas : ∀ n, Measurable (g n)

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

set_option warn.classDefReducibility false in
/-- `F_n := σ(X_0,…,X_n)` on the path space. -/
def pathFiltration (E : Type*) [MeasurableSpace E] (n : ℕ) : MeasurableSpace (ℕ → E) :=
  MeasurableSpace.comap (fun w : ℕ → E => fun i : Fin (n + 1) => w i) inferInstance

/-- `τ` is an `(F_n)`-**stopping time** (Definition 10.1.1, p. 304): `{τ ≤ n} ∈ F_n` for all `n`.
Values in `ℕ∞`. -/
def IsStopTime (tau : (ℕ → E) → ℕ∞) : Prop :=
  ∀ n : ℕ, MeasurableSet[pathFiltration E n] {w | tau w ≤ (n : ℕ∞)}

/-- The cylinder probability `ℙ^n_x(X_{n+1} ∈ B_0, …, X_{n+m} ∈ B_{m-1})`, by iterated integration
against `Q^X_n, Q^X_{n+1}, …`. -/
noncomputable def StoppingProblem.cyl (P : StoppingProblem E N) (t : ℕ) :
    ℕ → (ℕ → Set E) → E → ℝ≥0∞
  | 0, _, _ => 1
  | (m + 1), B, x => ∫⁻ y in B 0, P.cyl (t + 1) m (fun i => B (i + 1)) y ∂(P.QX t x)

/-- `Pr n x` is the law of `(X_n, X_{n+1}, …)` given `X_n = x` (reindexed to start at `0`),
pinned by its finite-dimensional distributions. -/
def StoppingProblem.IsPathLaw (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) : Prop :=
  (∀ n x, IsProbabilityMeasure (Pr n x)) ∧
  ∀ (n : ℕ) (x : E) (m : ℕ) (B : ℕ → Set E), (∀ i, MeasurableSet (B i)) →
    Pr n x {w : ℕ → E | ∀ i ≤ m, w i ∈ B i}
      = (B 0).indicator (fun y => P.cyl n m (fun i => B (i + 1)) y) x

/-- `R_τ = Σ_{k=0}^{τ-1} c_{n+k}(X_{n+k}) + g_{n+τ}(X_{n+τ})` for a path drawn from `Pr n x`
(`τ` counts steps from time `n`); `0` on `{τ = ∞}`, a convention never used since every
statement restricts to a.s. finite `τ`. -/
noncomputable def StoppingProblem.rewardFrom (P : StoppingProblem E N) (n : ℕ)
    (tau : (ℕ → E) → ℕ∞) (w : ℕ → E) : ℝ :=
  match tau w with
  | (m : ℕ) => (∑ k ∈ Finset.range m, P.c (n + k) (w k)) + P.g (n + m) (w m)
  | ⊤ => 0

/-- `𝔼^n_x[R_τ]` in `[-∞,∞]`. -/
noncomputable def StoppingProblem.EReward (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (n : ℕ) (tau : (ℕ → E) → ℕ∞) (x : E) : EReal :=
  erealIntegral (Pr n x) (fun w => (P.rewardFrom n tau w : EReal))

/-- **Assumption (B_N)** (p. 304): for `x ∈ E` and `0 ≤ n ≤ N`,
`sup_{n ≤ τ ≤ N} 𝔼^n_x[Σ_{k=n}^{τ-1} c_k^+(X_k) + g_τ^+(X_τ)] < ∞` (a Lebesgue integral, so the
bound is a genuine finiteness statement). -/
def StoppingProblem.AssumptionBN (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) : Prop :=
  ∀ (n : ℕ), n ≤ N → ∀ x : E, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ tau : (ℕ → E) → ℕ∞,
    IsStopTime tau → (∀ w, tau w ≤ ((N - n : ℕ) : ℕ∞)) →
      ∫⁻ w, ENNReal.ofReal ((∑ k ∈ Finset.range ((tau w).toNat), max (P.c (n + k) (w k)) 0)
          + max (P.g (n + (tau w).toNat) (w ((tau w).toNat))) 0) ∂(Pr n x) ≤ C

/-- `V_n(x) := sup_{n ≤ τ ≤ N} 𝔼^n_x[R_τ]`, the value of the stopping problem over `[n,N]`
(p. 306); `V_0 = V_N^*` is **(10.1)**. -/
noncomputable def StoppingProblem.Vn (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (n : ℕ) (x : E) : EReal :=
  ⨆ tau : (ℕ → E) → ℕ∞, ⨆ (_ : IsStopTime tau ∧ ∀ w, tau w ≤ ((N - n : ℕ) : ℕ∞)),
    P.EReward Pr n tau x

/-- `τ_π := inf{n ∈ ℕ_0 | f_n(X_n) = 1} ∧ N`, the stopping time of a Markov policy carried as
its stopping sets `S n = {f_n = 1}` (p. 305). -/
noncomputable def policyTime (S : ℕ → Set E) (N : ℕ) (w : ℕ → E) : ℕ∞ :=
  min (sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k})) (N : ℕ∞)

/-- `V_0(x) := sup_π V_{0π}(x)` over the Markov policies (measurable decision rules) of the
associated Markov Decision Model. -/
noncomputable def StoppingProblem.policyValue (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (x : E) : EReal :=
  ⨆ S : ℕ → Set E, ⨆ (_ : ∀ n, MeasurableSet (S n)), P.EReward Pr 0 (policyTime S N) x

/-- `T_n v(x) = max{g_n(x), c_n(x) + ∫ v(x') Q^X_n(dx'|x)}` (Theorem 10.1.3 a)), in `[-∞,∞]`. -/
noncomputable def StoppingProblem.T (P : StoppingProblem E N) (n : ℕ) (v : E → EReal) (x : E) :
    EReal :=
  max (P.g n x : EReal) ((P.c n x : EReal) + erealIntegral (P.QX n x) v)

/-- `τ^* := min{n ∈ ℕ_0 | X_n ∈ S_n} ∧ N`, the first entry into a time-dependent region, capped
at `N` (`inf ∅ = ∞`). -/
noncomputable def hitTimeCapped (S : ℕ → Set E) (N : ℕ) (w : ℕ → E) : ℕ∞ :=
  min (sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k})) (N : ℕ∞)

/-- `τ^* := inf{n ∈ ℕ_0 | X_n ∈ S}`, uncapped (`inf ∅ = ∞`). -/
noncomputable def hitTime (S : Set E) (w : ℕ → E) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S})

end MDPFinance.OptimalStopping
