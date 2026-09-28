import Mathlib

namespace LassoDantzig.Dantzig

/-- The empirical norm `‖f_j‖_n = ((1/n) ∑ᵢ X i j ²)^{1/2}` of the `j`-th column of the design
matrix `X = (f_j(Z_i))` (Bickel–Ritov–Tsybakov, p. 3). -/
noncomputable def colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, X i j ^ 2)

/-- The support `J(β) = {j : βⱼ ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- `|δ_J|_1 = ∑_{j ∈ J} |δⱼ|`, the ℓ1 norm of the restriction `δ_J` of `δ` to `J` (p. 4). -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δⱼ²)^{1/2}`, the ℓ2 norm of the restriction `δ_J` (p. 4). -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2 = (∑ᵢ vᵢ²)^{1/2}` of a vector `v ∈ ℝⁿ`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The general Dantzig constraint (p. 5), `|(1/n) D^{−1/2} Xᵀ(y − Xβ)|_∞ ≤ r` with
`D = diag(‖f₁‖_n², …, ‖f_M‖_n²)`, written coordinatewise:
`|(1/n) ∑ᵢ X i j (yᵢ − (Xβ)ᵢ)| ≤ r ‖fⱼ‖_n` for every `j`. -/
def DantzigConstraint {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r * colNorm X j

/-- `β̂` is a Dantzig selector in the general form (2.4), p. 5: it satisfies the general
Dantzig constraint and has the smallest (unweighted) ℓ1 norm `|β|_1 = ∑ⱼ |βⱼ|` among all
vectors that satisfy it. -/
def IsDantzigSelector {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  DantzigConstraint X y r βhat ∧
    ∀ β : Fin M → ℝ, DantzigConstraint X y r β → ∑ j, |βhat j| ≤ ∑ j, |β j|

/-- Membership in the set `Λ = {β ∈ ℝ^M : |(1/n) Xᵀ(y − Xβ)|_∞ ≤ r}` of the linear-regression
section (p. 16, under (7.3)), written coordinatewise:
`|(1/n) ∑ᵢ X i j (yᵢ − (Xβ)ᵢ)| ≤ r` for every `j`. -/
def InLambda {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r

/-- `β̂` is a Dantzig selector for the linear model (7.3), p. 16: `β̂ ∈ Λ` and
`|β̂|_1 ≤ |β|_1` for every `β ∈ Λ` (`β̂ ∈ argmin_{β ∈ Λ} |β|_1`). -/
def IsDantzig {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  InLambda X y r βhat ∧ ∀ β : Fin M → ℝ, InLambda X y r β → ∑ j, |βhat j| ≤ ∑ j, |β j|

/-- The noise event `ℬ = {|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r} = ⋂ⱼ {|Vⱼ| ≤ r ‖fⱼ‖_n}` (p. 23), as a
property of a realised noise vector `w ∈ ℝⁿ`, where `Vⱼ = (1/n) ∑ᵢ fⱼ(Zᵢ) wᵢ`. -/
def NoiseEvent {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

/-- The cone condition (4.1) (p. 9): `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`. -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- `J1` is an admissible choice of "the subset of `{1, …, M}` corresponding to the `m` largest
in absolute value coordinates of `δ` outside of `J0`" (p. 7): `J1 ⊆ J0ᶜ`, `|J1| = m`, and every
coordinate of `δ` in `J0ᶜ \ J1` is, in absolute value, at most every coordinate in `J1`. Under
ties several sets qualify. -/
def IsTopBlock {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ) : Prop :=
  J1 ⊆ J0ᶜ ∧ J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J₀ ⊆ {1, …, M}` with `|J₀| ≤ s`
and every `δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, `κ √n |δ_{J₀}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- Assumption RE(s, m, c₀) (p. 7) with witness `κ`: for every `J₀` with `|J₀| ≤ s`, every
`δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` and every admissible set `J₁` of the `m` largest
`|δⱼ|` outside `J₀`, `κ √n |δ_{J₀₁}|_2 ≤ |Xδ|_2` with `J₀₁ = J₀ ∪ J₁`. The paper's
`κ(s, m, c₀)` is the largest such `κ`. -/
def REm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 m →
      κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ)

end LassoDantzig.Dantzig
