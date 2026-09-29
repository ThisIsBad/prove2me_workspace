import Mathlib

namespace LassoDantzig.Lasso

/-- The ℓ1 norm `|δ|_1 = ∑ⱼ |δⱼ|` of a vector `δ ∈ ℝ^M` (Bickel–Ritov–Tsybakov, p. 4). -/
noncomputable def l1Norm {M : ℕ} (δ : Fin M → ℝ) : ℝ :=
  ∑ j, |δ j|

/-- `|δ_J|_1 = ∑_{j ∈ J} |δⱼ|`, the ℓ1 norm of the restriction `δ_J` of `δ` to `J` (p. 4). -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δⱼ²)^{1/2}`, the Euclidean norm of the restriction `δ_J` (p. 4). -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2 = (∑ᵢ vᵢ²)^{1/2}` of a vector `v ∈ ℝ^k`. -/
noncomputable def euclNorm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The squared empirical prediction loss `(1/n) |Xβ − f|_2² = (1/n) ∑ᵢ ((Xβ)ᵢ − fᵢ)²`
(p. 4; in Section 7, with `f = Xβ*`, this is `‖f_β − f‖_n² = |X(β − β*)|_2²/n`, p. 15). -/
noncomputable def predLoss {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ)
    (β : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X.mulVec β i - f i) ^ 2

/-- The support `J(β) = {j : βⱼ ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- The standing assumption of Section 7 (p. 15): every diagonal element of the Gram matrix
`Ψₙ = XᵀX/n` equals `1`, i.e. `‖f_j‖_n² = (1/n) ∑ᵢ X_{ij}² = 1` for every `j`. -/
def UnitDiag {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : Prop :=
  ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1

/-- `β̂` is a Lasso estimator (7.2), p. 15: it minimises
`(1/n) |y − Xβ|_2² + 2r |β|_1` over all `β ∈ ℝ^M`. -/
def IsLasso {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  ∀ β : Fin M → ℝ,
    (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec βhat i) ^ 2 + 2 * r * l1Norm βhat ≤
      (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec β i) ^ 2 + 2 * r * l1Norm β

/-- `φ_max`, the maximal eigenvalue of the Gram matrix `Ψₙ = XᵀX/n` (p. 5, p. 20), as the
Rayleigh supremum `sup {(1/n) |Xx|_2² : x ∈ ℝ^M, |x|_2 = 1}`. The set is nonempty when `M ≥ 1`
and bounded above, so the supremum is the largest eigenvalue of the symmetric positive
semidefinite matrix `Ψₙ`. -/
noncomputable def phiMax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  sSup {t : ℝ | ∃ x : Fin M → ℝ, ∑ j, x j ^ 2 = 1 ∧ t = (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2}

/-- The cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` of (4.1) and Assumption RE(s, c₀) (p. 7). -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J₀ ⊆ {1, …, M}` with `|J₀| ≤ s`
and every `δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, `κ √n |δ_{J₀}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- `J₁` is a set of `m` indices outside `J₀` carrying `m` largest absolute values among the
coordinates of `δ` outside `J₀` (p. 7). Under ties several sets qualify; they all give the same
`|δ_{J₀ ∪ J₁}|_2`. -/
def IsTopOutside {M : ℕ} (m : ℕ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ)
    (J1 : Finset (Fin M)) : Prop :=
  J1 ⊆ J0ᶜ ∧ J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|

/-- Assumption RE(s, m, c₀) (p. 7) with witness `κ`: for every `J₀` with `|J₀| ≤ s`, every
`δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, and every set `J₁` of the `m` largest in absolute
value coordinates of `δ` outside `J₀`, `κ √n |δ_{J₀₁}|_2 ≤ |Xδ|_2` with `J₀₁ = J₀ ∪ J₁`.
The paper's `κ(s, m, c₀)` is the largest such `κ`. -/
def REm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    ∀ J1 : Finset (Fin M), IsTopOutside m J0 δ J1 →
      κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ)

/-- The noise event `𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r}` (p. 21, with `r_{n,j} = r‖f_j‖_n = r` under the unit
diagonal of Section 7), as a property of a realised noise vector `w ∈ ℝⁿ`, where
`Vⱼ = (1/n) ∑ᵢ X_{ij} wᵢ`. -/
def NoiseEventHalf {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r

end LassoDantzig.Lasso
