import Mathlib

namespace PrescAnalytics.ERM

open MeasureTheory Filter Topology

/-- A Rademacher sign `σ ∈ {+1, −1}` encoded by a Boolean: `true ↦ +1`, `false ↦ −1`. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- For a fixed sign matrix `σ ∈ {±1}^{N×d}` and a sample `s = (s_1, …, s_N)`, the supremum
`sup_{g ∈ F} Σ_{i=1}^N Σ_{k=1}^d σ_{ik} g_k(s_i)` (Definition 3, p. 39), computed in `EReal`:
it is `+∞` when the sums are unbounded above over `F`, and `−∞` when `F` is empty. -/
noncomputable def signedSup {U : Type*} {d N : ℕ} (F : Set (U → Fin d → ℝ)) (s : Fin N → U)
    (σ : Fin N → Fin d → Bool) : EReal :=
  ⨆ g ∈ F, ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal)

/-- Definition 3 (p. 39): the empirical multivariate Rademacher complexity
`ℜ̂_N(F; S_N) = E_σ[(2/N) sup_{g ∈ F} Σ_i Σ_k σ_{ik} g_k(s_i)]` of a class `F` of `ℝ^d`-valued
functions on the sample `s`, where the `σ_{ik}` are i.i.d. uniform signs: the expectation is the
average over all `2^{N d}` sign matrices. Factor `2/N`, no absolute value; value in `EReal`. -/
noncomputable def empRademacher {U : Type*} {d N : ℕ} (F : Set (U → Fin d → ℝ))
    (s : Fin N → U) : EReal :=
  (((2 : ℝ) / N / 2 ^ (N * d) : ℝ) : EReal) * ∑ σ : Fin N → Fin d → Bool, signedSup F s σ

/-- Definition 3 (p. 39): the marginal multivariate Rademacher complexity
`ℜ_N(F) = E[ℜ̂_N(F; S_N)]`, the expectation over an i.i.d. sample `S_N ∼ ν^N`, as a lower Lebesgue
integral in `ℝ≥0∞` of the empirical complexity (which is `≥ 0` for a nonempty class). -/
noncomputable def margRademacher {U : Type*} [MeasurableSpace U] {d : ℕ} (ν : Measure U) (N : ℕ)
    (F : Set (U → Fin d → ℝ)) : ENNReal :=
  ∫⁻ s, (empRademacher F s).toENNReal ∂(Measure.pi fun _ : Fin N => ν)

/-- A real-valued class `G` viewed as a class of `ℝ^1`-valued functions `u ↦ (g u)`. -/
def liftClass {U : Type*} (G : Set (U → ℝ)) : Set (U → Fin 1 → ℝ) :=
  (fun g u _ => g u) '' G

/-- The univariate empirical Rademacher complexity `ℜ̂_N(G; S_N)` of a real-valued class: Definition 3
with `d = 1` ("when `d = 1` the above definition coincides with the common definition", p. 39). -/
noncomputable def empRademacherR {U : Type*} {N : ℕ} (G : Set (U → ℝ)) (s : Fin N → U) : EReal :=
  empRademacher (liftClass G) s

/-- The univariate marginal Rademacher complexity `ℜ_N(G)`: Definition 3 with `d = 1`. -/
noncomputable def margRademacherR {U : Type*} [MeasurableSpace U] (ν : Measure U) (N : ℕ)
    (G : Set (U → ℝ)) : ENNReal :=
  margRademacher ν N (liftClass G)

/-- The empirical mean `(1/N) Σ_{i=1}^N g(u^i)` of `g` on the sample `s = (u^1, …, u^N)`. -/
noncomputable def empMean {U : Type*} {N : ℕ} (s : Fin N → U) (g : U → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, g (s i)

/-- The cost class `𝒢 = {(x, y) ↦ c(f(x); y) : f ∈ F}` of Lemma 1 (p. 40) and of the proof of
Theorem 13 (p. 41), for a cost `c(z; y)` with decisions `z ∈ ℝ^d`. -/
def costClass {X Y : Type*} {d : ℕ} (c : (Fin d → ℝ) → Y → ℝ) (F : Set (X → Fin d → ℝ)) :
    Set (X × Y → ℝ) :=
  {g | ∃ f ∈ F, g = fun p => c (f p.1) p.2}

/-- The expected cost `E[c(z(X); Y)] = ∫ c(z(x); y) dμ(x, y)` of a decision rule `z(·)` (Bochner
integral; integrable when `c` is bounded and measurable and `z` is measurable). -/
noncomputable def expCost {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (μ : Measure (X × Y)) (c : (Fin d → ℝ) → Y → ℝ) (z : X → Fin d → ℝ) : ℝ :=
  ∫ p, c (z p.1) p.2 ∂μ

/-- The empirical cost `(1/N) Σ_{i=1}^N c(z(x^i); y^i)` of a decision rule on the sample
`s = ((x^1, y^1), …, (x^N, y^N))`, the objective of (4). -/
noncomputable def empCost {X Y : Type*} {d N : ℕ} (s : Fin N → X × Y)
    (c : (Fin d → ℝ) → Y → ℝ) (z : X → Fin d → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, c (z (s i).1) (s i).2

/-- A class `F` of functions `U → V` is *pointwise separable* when it has a countable subclass `F₀`
such that every `f ∈ F` is the pointwise limit of a sequence in `F₀`. This is the standard
measurability convention under which the suprema over `F` that the paper takes expectations and
probabilities of are measurable (it holds for the linear rules (25)). -/
def IsPointwiseSeparable {U V : Type*} [TopologicalSpace V] (F : Set (U → V)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ u : ℕ → U → V, (∀ n, u n ∈ F₀) ∧
    ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))

end PrescAnalytics.ERM
