import Mathlib

namespace LassoDantzig.Oracle

open MeasureTheory ProbabilityTheory

/-- The squared empirical norm `‖v‖_n² = (1/n) ∑ᵢ vᵢ²` of a vector `v ∈ ℝⁿ` of values
`v = (g(Z_1), …, g(Z_n))` (Bickel–Ritov–Tsybakov, p. 3). -/
noncomputable def empSq {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, v i ^ 2

/-- The empirical norm `‖v‖_n = √((1/n) ∑ᵢ vᵢ²)` (p. 3). -/
noncomputable def empNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (empSq v)

/-- The empirical norm `‖f_j‖_n` of the `j`-th dictionary function, i.e. of the `j`-th column of
the design matrix `X = (f_j(Z_i))` (p. 4). -/
noncomputable def colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : ℝ :=
  empNorm (fun i => X i j)

/-- `f_max = max_j ‖f_j‖_n` (p. 4). For `M ≥ 1` the supremum of the finitely many values is
their maximum. -/
noncomputable def fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  ⨆ j : Fin M, colNorm X j

/-- `f_min = min_j ‖f_j‖_n` (p. 4). For `M ≥ 1` the infimum of the finitely many values is
their minimum. -/
noncomputable def fmin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  ⨅ j : Fin M, colNorm X j

/-- The support `J(β) = {j : β_j ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- `|δ_J|_1 = ∑_{j ∈ J} |δ_j|`. -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δ_j²)^{1/2}`. -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2` of a vector `v ∈ ℝⁿ`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` (p. 7, inside Assumption RE(s, c₀)). -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J0` with `|J0| ≤ s` and every
`δ ≠ 0` with `|δ_{J0ᶜ}|_1 ≤ c₀ |δ_{J0}|_1`, `κ √n |δ_{J0}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- The single-set restricted eigenvalue inequality with constant `γ` at the index set `J0`:
for every `δ ≠ 0` with `|δ_{J0ᶜ}|_1 ≤ c₀ |δ_{J0}|_1`, `γ √n |δ_{J0}|_2 ≤ |Xδ|_2`, i.e.
`min_{δ ≠ 0, cone} |Xδ|_2 / (√n |δ_{J0}|_2) ≥ γ` (p. 13; the minimum over an empty set is `+∞`). -/
def REAt {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (c0 γ : ℝ) (J0 : Finset (Fin M)) : Prop :=
  ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    γ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- The index family `𝒥_{s,γ,c₀} = {J0 : |J0| ≤ s, min_{δ ≠ 0, cone} |Xδ|_2/(√n|δ_{J0}|_2) ≥ γ}`
(p. 13). -/
def JFamily {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (γ c0 : ℝ)
    (J0 : Finset (Fin M)) : Prop :=
  J0.card ≤ s ∧ REAt X c0 γ J0

/-- The set `Λ_{s,γ,c₀} = {β : J(β) ∈ 𝒥_{s,γ,c₀}}` (p. 13). -/
def LambdaSet {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (γ c0 : ℝ) :
    Set (Fin M → ℝ) :=
  {β | JFamily X s γ c0 (supp β)}

/-- The Lasso criterion (2.1) (p. 4):
`Ŝ(β) + 2r ∑_j ‖f_j‖_n |β_j|` with `Ŝ(β) = (1/n) ∑ᵢ (Y_i − (Xβ)_i)²`. -/
noncomputable def lassoObj {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : ℝ :=
  empSq (fun i => y i - X.mulVec β i) + 2 * r * ∑ j, colNorm X j * |β j|

/-- `β̂` is a Lasso solution (2.1): it minimises the Lasso criterion over all of `ℝ^M`.
(Minimisers need not be unique; statements are made for every minimiser.) -/
def IsLasso {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  ∀ β : Fin M → ℝ, lassoObj X y r βhat ≤ lassoObj X y r β

/-- The tuning constant `r = A σ √(log M / n)` of Lemma B.1 and Theorem 6.1 (natural log). -/
noncomputable def tuning (n M : ℕ) (A σ : ℝ) : ℝ :=
  A * σ * Real.sqrt (Real.log M / n)

/-- The noise model of Section 2: `W_1, …, W_n` are measurable, independent, and each
`W_i ∼ N(0, σ²)`. -/
def GaussianNoise {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (W : Fin n → Ω → ℝ) (σ : ℝ) : Prop :=
  (∀ i, Measurable (W i)) ∧ iIndepFun W P ∧
    ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal

/-- The random variable `V_j = n⁻¹ ∑ᵢ f_j(Z_i) W_i` (p. 21). -/
noncomputable def noiseCorr {Ω : Type*} {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (W : Fin n → Ω → ℝ) (j : Fin M) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, X i j * W i ω

/-- The event `𝒜 = ⋂_j {2|V_j| ≤ r_{n,j}}` with `r_{n,j} = r ‖f_j‖_n` (p. 21). -/
def noiseEvent {Ω : Type*} {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (W : Fin n → Ω → ℝ)
    (r : ℝ) : Set Ω :=
  {ω | ∀ j, 2 * |noiseCorr X W j ω| ≤ r * colNorm X j}

/-- The deterministic form of the event `𝒜` for a fixed noise vector `w = y − f`:
`2 |n⁻¹ ∑ᵢ X_{ij} w_i| ≤ r ‖f_j‖_n` for every `j`. -/
def NoiseBound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ) (r : ℝ) : Prop :=
  ∀ j, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

end LassoDantzig.Oracle
