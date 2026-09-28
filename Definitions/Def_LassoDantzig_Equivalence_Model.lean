import Mathlib

namespace LassoDantzig.Equivalence

/-- The empirical norm `‖g‖_n = ((1/n) ∑ᵢ g(Zᵢ)²)^{1/2}` of a vector of values
`g = (g(Z₁), …, g(Zₙ)) ∈ ℝⁿ` (Bickel–Ritov–Tsybakov, p. 3). -/
noncomputable def empNorm {n : ℕ} (g : Fin n → ℝ) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, g i ^ 2)

/-- The empirical norm `‖f_j‖_n` of the `j`-th dictionary function, i.e. of the `j`-th column
of the design matrix `X = (f_j(Z_i))` (p. 3). -/
noncomputable def colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : ℝ :=
  empNorm (fun i => X i j)

/-- `f_max = max_{1 ≤ j ≤ M} ‖f_j‖_n` (p. 4). The supremum of finitely many reals; it is the
maximum whenever `M ≥ 1`. -/
noncomputable def fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  ⨆ j : Fin M, colNorm X j

/-- The squared empirical prediction loss `‖f_β − f‖_n² = (1/n) ∑ᵢ ((Xβ)ᵢ − f(Zᵢ))²` of the
linear combination `f_β = ∑ⱼ βⱼ fⱼ` (whose vector of values is `Xβ`), p. 4. -/
noncomputable def predLoss {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ)
    (β : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X.mulVec β i - f i) ^ 2

/-- The support `J(β) = {j : βⱼ ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- `|δ_J|_1 = ∑_{j ∈ J} |δⱼ|`, the ℓ1 norm of the restriction `δ_J` (p. 4). -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δⱼ²)^{1/2}`, the ℓ2 norm of the restriction `δ_J` (p. 4). -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2` of a vector `v ∈ ℝⁿ`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Lasso criterion (2.1), p. 4:
`Ŝ(β) + 2r ∑ⱼ ‖fⱼ‖_n |βⱼ|` with `Ŝ(β) = (1/n) ∑ᵢ (Yᵢ − f_β(Zᵢ))²`. -/
noncomputable def lassoObj {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec β i) ^ 2 + 2 * r * ∑ j, colNorm X j * |β j|

/-- `β̂` is a Lasso solution (2.1): it minimises the Lasso criterion over all of `ℝ^M`. -/
def IsLasso {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  ∀ β : Fin M → ℝ, lassoObj X y r βhat ≤ lassoObj X y r β

/-- The Dantzig constraint (p. 5), `|(1/n) D^{−1/2} Xᵀ(y − Xβ)|_∞ ≤ r` with
`D = diag(‖f₁‖_n², …, ‖f_M‖_n²)`, written coordinatewise:
`|(1/n) ∑ᵢ X i j (yᵢ − (Xβ)ᵢ)| ≤ r ‖fⱼ‖_n` for every `j`. -/
def DantzigFeasible {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r * colNorm X j

/-- `β̂` is a Dantzig selector (2.4), p. 5: it satisfies the Dantzig constraint and has the
smallest (unweighted) ℓ1 norm `|β|_1 = ∑ⱼ |βⱼ|` among all vectors satisfying it. -/
def IsDantzig {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  DantzigFeasible X y r βhat ∧
    ∀ β : Fin M → ℝ, DantzigFeasible X y r β → ∑ j, |βhat j| ≤ ∑ j, |β j|

/-- The cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` of Assumption RE(s, c₀) (p. 7). -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J₀ ⊆ {1, …, M}` with `|J₀| ≤ s`
and every `δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, `κ √n |δ_{J₀}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- The noise event `𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r ‖fⱼ‖_n}` (p. 21), as a property of a realised noise
vector `w ∈ ℝⁿ`, where `Vⱼ = (1/n) ∑ᵢ fⱼ(Zᵢ) wᵢ`. Equivalently (B.5):
`|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r/2`. -/
def NoiseEventHalf {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

/-- The noise event `ℬ = ⋂ⱼ {|Vⱼ| ≤ r ‖fⱼ‖_n} = {|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r}` (p. 23), as a
property of a realised noise vector `w ∈ ℝⁿ`. -/
def NoiseEvent {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

end LassoDantzig.Equivalence
