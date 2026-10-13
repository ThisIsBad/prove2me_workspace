import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_ISIModel

namespace BertsekasShreve.ImperfectInfo

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {S C Z : Type}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
  [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- Definition 10.6 (pp. 250–251): a statistic `(η₀, …, η_{N−1})`, `η_k : P(S) I_k → Y_k`
Borel-measurable with `Y_k` a nonempty Borel space, which is *sufficient for control* for the
model (ISI) `M`. The structure carries the witnesses of conditions (a)–(c):
* (a) analytic sets `Γ̂_k ⊆ Y_k C` with `proj_{Y_k}(Γ̂_k) = Y_k` and
  `Γ_k = {(i_k, u) | (η_k(p; i_k), u) ∈ Γ̂_k}` for every `p` (eq. (20));
* (b) Borel stochastic kernels `t̂_k(dy_{k+1} | y_k, u_k)` on `Y_{k+1}` given `Y_k C`,
  `k = 0, …, N−2`, such that for every `p`, `π ∈ Π` and Borel `B ⊆ Y_{k+1}`,
  `P_{k+1}(π,p)[η_{k+1}(p;i_{k+1}) ∈ B | η_k(p;i_k) = y_k, u_k = u_k] = t̂_k(B | y_k, u_k)`
  (eq. (22)), stated through the defining relation of conditional probability: integrated
  over every event `{(η_k, u_k) ∈ A}`, `A` Borel;
* (c) lower semianalytic `ĝ_k : Γ̂_k → R*` with
  `E[g(x_k, u_k) | η_k(p;i_k) = y_k, u_k = u_k] = ĝ_k(y_k, u_k)` (eq. (23)), stated through
  the defining relation `∫_D g dP_k = ∫_D ĝ_k(η_k, u_k) dP_k` for every event
  `D = {(η_k, u_k) ∈ A}`, whenever `g(x_k, u_k)` is quasi-integrable for `P_k(π,p)` (the
  standing assumption under which the book defines conditional expectations, p. 246).

The families `Y`, `Γ̂`, `t̂`, `ĝ` are indexed by all `k : ℕ`; only the book's indices
(`k < N`, resp. `k + 1 < N` for `t̂`) are constrained. -/
structure SuffStat {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) (Y : ℕ → Type)
    [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)] where
  borel_Y : ∀ k, BorelSpace (Y k)
  isBorel_Y : ∀ k, IsBorelSpace (Y k)
  nonempty_Y : ∀ k, Nonempty (Y k)
  /-- the statistic `η_k(p; i_k)` -/
  η : (k : ℕ) → ProbabilityMeasure S × Info Z C k → Y k
  η_measurable : ∀ k, Measurable (η k)
  /-- (a) the sets `Γ̂_k ⊆ Y_k C` -/
  Γhat : (k : ℕ) → Set (Y k × C)
  Γhat_analytic : ∀ k < M.N, MeasureTheory.AnalyticSet (Γhat k)
  Γhat_proj : ∀ k < M.N, Prod.fst '' Γhat k = Set.univ
  Gamma_eq : ∀ k < M.N, ∀ p : ProbabilityMeasure S,
    GammaSet M.U k = {q | (η k (p, q.1), q.2) ∈ Γhat k}
  /-- (b) the kernels `t̂_k(dy_{k+1} | y_k, u_k)` -/
  that : (k : ℕ) → Kernel (Y k × C) (Y (k + 1))
  that_markov : ∀ k, k + 1 < M.N → IsMarkovKernel (that k)
  cond_trans : ∀ k, k + 1 < M.N →
    ∀ π, M.IsPolicy π → ∀ (p : ProbabilityMeasure S) (A : Set (Y k × C)) (B : Set (Y (k + 1))),
      MeasurableSet A → MeasurableSet B →
      M.law π p (k + 1)
          {h | (η k (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A ∧
            η (k + 1) (p, ISIModel.infoOf h.obs) ∈ B} =
        ∫⁻ h, A.indicator (fun yu => that k yu B)
            (η k (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∂(M.law π p (k + 1))
  /-- (c) the costs `ĝ_k : Γ̂_k → R*` -/
  ghat : (k : ℕ) → Y k × C → EReal
  ghat_lsa : ∀ k < M.N, LowerSemianalyticOn (ghat k) (Γhat k)
  cond_cost : ∀ k < M.N, ∀ π, M.IsPolicy π → ∀ p : ProbabilityMeasure S,
    QuasiIntegrable (M.law π p k) (fun h => M.g (h.state.1, h.control)) →
    ∀ A : Set (Y k × C), MeasurableSet A →
      extIntegral ((M.law π p k).restrict {h | (η k (p, ISIModel.infoOf h.obs), h.control) ∈ A})
          (fun h => M.g (h.state.1, h.control)) =
        extIntegral ((M.law π p k).restrict {h | (η k (p, ISIModel.infoOf h.obs), h.control) ∈ A})
          (fun h => ghat k (η k (p, ISIModel.infoOf h.obs), h.control))

/-- A Markov (PSI) policy `μ̂_k(du | y_k)` viewed as a policy in `Π̂'`, i.e. as a kernel on
the whole observed history `(y₀, u₀, …, y_k)` that depends only on `y_k`. -/
def markovToPolicy {C : Type} [MeasurableSpace C] {Y : ℕ → Type} (μ : (k : ℕ) → Y k → ProbabilityMeasure C) :
    (n : ℕ) → Obs Y C n → ProbabilityMeasure C :=
  fun n o => μ n (o.1 (Fin.last n))

namespace SuffStat

variable {M : ISIModel S C Z} {Y : ℕ → Type}
  [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)] (σ : SuffStat M Y)

/-! ### The perfect state information model (PSI), Definition 10.7 (p. 251)

States `Y_k`, control space `C`, control constraints `Û_k`, discount factor `α`, costs `ĝ_k`,
transition kernels `t̂_k`, horizon `N`. -/

/-- `Û_k(y_k) = (Γ̂_k)_{y_k}`, the section of `Γ̂_k` at `y_k` (eq. (21)). -/
def Uhat (k : ℕ) (y : Y k) : Set C := {u | (y, u) ∈ σ.Γhat k}

/-- (PSI) policies `Π̂'` (0-originating, Definition 10.1 specialized to (PSI)):
`μ̂_k(du_k | y₀, u₀, …, u_{k−1}, y_k)` universally measurable with
`μ̂_k(Û_k(y_k) | y₀, …, y_k) = 1` for `k < N`. -/
def IsPolicy (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) : Prop :=
  (∀ n, UnivMeasurable (μ n)) ∧
    ∀ n < M.N, ∀ o : Obs Y C n, (μ n o : Measure C) (σ.Uhat n (o.1 (Fin.last n))) = 1

/-- Markov (PSI) policies `Π̂`: `μ̂_k(du_k | y_k)` universally measurable with
`μ̂_k(Û_k(y_k) | y_k) = 1` for `k < N`. -/
def IsMarkovPolicy (μ : (k : ℕ) → Y k → ProbabilityMeasure C) : Prop :=
  (∀ k, UnivMeasurable (μ k)) ∧ ∀ k < M.N, ∀ y : Y k, (μ k y : Measure C) (σ.Uhat k y) = 1

/-- The probability measures `P̂_k(π̂, q)` on `Y₀C₀⋯Y_kC_k` (eq. (28), p. 252). -/
noncomputable def lawHat (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) (q : Measure (Y 0))
    (k : ℕ) : Measure (Hist Y C k) :=
  histLaw q σ.that (fun n o => (μ n o : Measure C)) k

/-- The (0-originating) cost of `π̂` for (PSI) at `y ∈ Y₀` (eq. (31), p. 254):
`Ĵ_{N,π̂}(y) = ∑_{k=0}^{N−1} α^k ∫ ĝ_k(y_k, u_k) dP̂_k(π̂, p_y)`, `p_y` the point mass at `y`. -/
noncomputable def costHat (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) (y : Y 0) : EReal :=
  BertsekasShreve.BorelFinite.bsum (List.ofFn fun k : Fin M.N =>
    ((M.α ^ (k : ℕ) : ℝ) : EReal) *
      extIntegral (σ.lawHat μ (Measure.dirac y) k) (fun h => σ.ghat k (h.state, h.control)))

/-- The (0-originating) optimal cost of (PSI): `Ĵ*_N(y) = inf_{π̂ ∈ Π̂'} Ĵ_{N,π̂}(y)` (eq. (32)). -/
noncomputable def optCostHat (y : Y 0) : EReal :=
  ⨅ μ : {μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C // σ.IsPolicy μ}, σ.costHat μ.1 y

/-- `k`-originating (PSI) policies `Π̂^k` (Definition 10.1): kernels
`μ̂_{k+n}(du | y_k, u_k, …, y_{k+n})` on the histories of the shifted state spaces
`Y_k, Y_{k+1}, …`, with `μ̂_{k+n}(Û_{k+n}(y_{k+n}) | …) = 1` for `k + n < N`. -/
def IsPolicyFrom (k : ℕ)
    (μ : (n : ℕ) → Obs (fun j => Y (k + j)) C n → ProbabilityMeasure C) : Prop :=
  (∀ n, UnivMeasurable (μ n)) ∧
    ∀ n, k + n < M.N → ∀ o : Obs (fun j => Y (k + j)) C n,
      (μ n o : Measure C) (σ.Uhat (k + n) (o.1 (Fin.last n))) = 1

/-- The `k`-originating distributions of `(y_k, u_k, …, y_{k+n}, u_{k+n})` for (PSI) started at
`y_k ∈ Y_k` (eq. (2) of Chapter 10, whose marginal on `Y_{k+n}C` is `q̂_{k+n}(π̂^k, p_{y_k})`). -/
noncomputable def lawHatFrom (k : ℕ)
    (μ : (n : ℕ) → Obs (fun j => Y (k + j)) C n → ProbabilityMeasure C) (y : Y k) (n : ℕ) :
    Measure (Hist (fun j => Y (k + j)) C n) :=
  histLaw (X := fun j => Y (k + j)) (Measure.dirac y) (fun j => σ.that (k + j))
    (fun m o => (μ m o : Measure C)) n

/-- Assumption (F̂⁺): (F⁺) of Section 10.1 (p. 244) for (PSI):
`∫ ĝ_j⁻ dq̂_j(π̂^k, p_{y_k}) < ∞` for all `π̂^k ∈ Π̂^k`, `y_k ∈ Y_k`, `k ≤ j ≤ N−1`. -/
def FhatPlus : Prop :=
  ∀ k < M.N, ∀ μ, σ.IsPolicyFrom k μ → ∀ (y : Y k) (n : ℕ), k + n < M.N →
    ∫⁻ h, negPart (σ.ghat (k + n) (h.state, h.control)) ∂(σ.lawHatFrom k μ y n) < ∞

/-- Assumption (F̂⁻): (F⁻) of Section 10.1 (p. 244) for (PSI):
`∫ ĝ_j⁺ dq̂_j(π̂^k, p_{y_k}) < ∞` for all `π̂^k ∈ Π̂^k`, `y_k ∈ Y_k`, `k ≤ j ≤ N−1`. -/
def FhatMinus : Prop :=
  ∀ k < M.N, ∀ μ, σ.IsPolicyFrom k μ → ∀ (y : Y k) (n : ℕ), k + n < M.N →
    ∫⁻ h, posPart (σ.ghat (k + n) (h.state, h.control)) ∂(σ.lawHatFrom k μ y n) < ∞

/-- The map `φ : P(S) → P(Y₀)` of eq. (26) (p. 252):
`φ(p)(B) = ∫_S s₀({z₀ | η₀(p; z₀) ∈ B} | x₀) p(dx₀)`, i.e. the image of `p ⊗ s₀` under
`(x₀, z₀) ↦ η₀(p; z₀)`. -/
noncomputable def phi (p : ProbabilityMeasure S) : Measure (Y 0) :=
  Measure.map (fun xz : S × Z => σ.η 0 (p, ((fun _ => xz.2), fun i => Fin.elim0 i)))
    ((p : Measure S) ⊗ₘ M.s0)

/-- A Markov (PSI) policy `π̂ = (μ̂₀, μ̂₁, …)` regarded as a policy for (ISI) (p. 252):
`μ_k(du | p; i_k) = μ̂_k(du | η_k(p; i_k))`. -/
def toISI (μ : (k : ℕ) → Y k → ProbabilityMeasure C) :
    (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C :=
  fun k pi => μ k (σ.η k pi)

/-- The mapping `V_{p,k} : H_k → Y₀C₀⋯Y_kC_k`,
`V_{p,k}(x₀, z₀, u₀, …, x_k, z_k, u_k) = (η₀(p; i₀), u₀, …, η_k(p; i_k), u_k)` (eq. (27)),
where `i_j = (z₀, u₀, …, u_{j−1}, z_j)`. -/
def V (p : ProbabilityMeasure S) (k : ℕ) (h : Hist (fun _ => S × Z) C k) : Hist Y C k :=
  (fun m => σ.η m (p, ((fun j => (h.1 ⟨j, by omega⟩).2), fun j => h.2 ⟨j, by omega⟩)), h.2)

/-- Definition 10.8 (p. 256): given `q ∈ P(Y₀)` and `ε > 0`, `π̂ ∈ Π̂'` is *weakly `q`-`ε`-optimal*
if `∫ Ĵ_{N,π̂} dq ≤ ∫ Ĵ*_N dq + ε` when `∫ Ĵ*_N dq > −∞`, and `∫ Ĵ_{N,π̂} dq ≤ −1/ε` when
`∫ Ĵ*_N dq = −∞`. -/
def IsWeaklyEpsOptimal (q : Measure (Y 0)) (ε : ℝ)
    (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) : Prop :=
  σ.IsPolicy μ ∧
    (⊥ < extIntegral q σ.optCostHat →
      extIntegral q (σ.costHat μ) ≤ extIntegral q σ.optCostHat + (ε : EReal)) ∧
    (extIntegral q σ.optCostHat = ⊥ → extIntegral q (σ.costHat μ) ≤ ((-1 / ε : ℝ) : EReal))

/-- Definition 10.8 (p. 256): `π̂ ∈ Π̂'` is *`q`-optimal* if
`q({y₀ | Ĵ_{N,π̂}(y₀) = Ĵ*_N(y₀)}) = 1`. -/
def IsQOptimal (q : Measure (Y 0)) (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) : Prop :=
  σ.IsPolicy μ ∧ q {y | σ.costHat μ y = σ.optCostHat y} = 1

/-- `π̂ ∈ Π̂'` is optimal for (PSI): `Ĵ_{N,π̂}(y₀) = Ĵ*_N(y₀)` for every `y₀ ∈ Y₀` (p. 244). -/
def IsOptimalHat (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) : Prop :=
  σ.IsPolicy μ ∧ ∀ y, σ.costHat μ y = σ.optCostHat y

/-- `π̂ ∈ Π̂'` is `ε`-optimal for (PSI) (p. 244): for every `y₀ ∈ Y₀`,
`Ĵ_{N,π̂}(y₀) ≤ Ĵ*_N(y₀) + ε` if `Ĵ*_N(y₀) > −∞` and `Ĵ_{N,π̂}(y₀) ≤ −1/ε` otherwise. -/
def IsEpsOptimalHat (ε : ℝ) (μ : (n : ℕ) → Obs Y C n → ProbabilityMeasure C) : Prop :=
  σ.IsPolicy μ ∧ ∀ y,
    (⊥ < σ.optCostHat y → σ.costHat μ y ≤ σ.optCostHat y + (ε : EReal)) ∧
    (σ.optCostHat y = ⊥ → σ.costHat μ y ≤ ((-1 / ε : ℝ) : EReal))

end SuffStat

end BertsekasShreve.ImperfectInfo
