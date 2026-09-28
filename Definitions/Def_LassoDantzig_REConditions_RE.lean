import Mathlib

namespace LassoDantzig.REConditions

/-- The restriction `δ_J` of a vector `δ ∈ ℝ^M` to an index set `J`: it agrees with `δ` on `J`
and vanishes off `J` (Bickel–Ritov–Tsybakov, p. 4). -/
def restrict {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : Fin M → ℝ :=
  fun j => if j ∈ J then δ j else 0

/-- `|δ_J|_1 = ∑_{j ∈ J} |δ_j|`. -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δ_j²)^{1/2}`. -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2` of a vector `v ∈ ℝ^n`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The support `J(x) = {j : x_j ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (x : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => x j ≠ 0)

/-- The sparsity `𝓜(x) = |J(x)|`, the number of non-zero coordinates (p. 4). -/
noncomputable def sparsity {M : ℕ} (x : Fin M → ℝ) : ℕ :=
  (supp x).card

/-- The cone condition (4.1) (p. 9): `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`. -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- `J1` is an admissible choice of "the set of the `m` largest in absolute value coordinates of
`δ` outside of `J0`" (p. 7): `J1 ⊆ J0ᶜ`, `|J1| = m`, and every coordinate of `δ` in
`J0ᶜ \ J1` is at most, in absolute value, every coordinate in `J1`. Under ties several sets
qualify; statements quantify over all of them. -/
def IsTopBlock {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ) : Prop :=
  J1 ⊆ J0ᶜ ∧ J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J0` with `|J0| ≤ s` and every
`δ ≠ 0` satisfying the cone condition (4.1), `κ √n |δ_{J0}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- Assumption RE(s, m, c₀) (p. 7) with witness `κ`: as `RE`, but with `|δ_{J01}|_2` in the
denominator, `J01 = J0 ∪ J1`, for every admissible `J1` (the `m` largest `|δ_j|` outside `J0`). -/
def REm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 m →
      κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ)

/-- The blocks `J 1, …, J K` form a partition of the index set `S`: pairwise disjoint, with union
`S`. (Blocks may be empty; `K ≥ 1`.) -/
def IsBlockPartition {M : ℕ} (S : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ) : Prop :=
  1 ≤ K ∧
  (∀ k ∈ Finset.Icc 1 K, ∀ l ∈ Finset.Icc 1 K, k ≠ l → Disjoint (J k) (J l)) ∧
  (Finset.Icc 1 K).biUnion J = S

/-- The partition of `J0ᶜ` used in Appendix A (p. 19): `J0ᶜ = J 1 ∪ ⋯ ∪ J K`, `|J k| = m` for
`k = 1, …, K − 1`, `|J K| ≤ m`, and the blocks are sorted by decreasing absolute value of `δ`
(every coordinate in a later block is at most every coordinate in an earlier one), so that `J k`
is the set of the `m` largest `|δ_j|` outside `J 1 ∪ ⋯ ∪ J (k − 1)` for `k < K`, and `J K` is the
remaining set. -/
def IsShelling {M : ℕ} (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (m : ℕ)
    (J : ℕ → Finset (Fin M)) (K : ℕ) : Prop :=
  IsBlockPartition J0ᶜ J K ∧
  (∀ k ∈ Finset.Ico 1 K, (J k).card = m) ∧
  (J K).card ≤ m ∧
  ∀ k ∈ Finset.Icc 1 K, ∀ l ∈ Finset.Icc 1 K, k < l → ∀ a ∈ J k, ∀ b ∈ J l, |δ b| ≤ |δ a|

/-- The linear span in `ℝⁿ` of the columns of `X` indexed by `J`, i.e. of the columns of `X_J`. -/
noncomputable def colSpan {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (J : Finset (Fin M)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ ((fun j => WithLp.toLp 2 (fun i => X i j)) '' (J : Set (Fin M)))

/-- `|P_J v|_2`: the Euclidean norm of the orthogonal projection of `v ∈ ℝⁿ` onto the span of
the columns of `X_J` (the projector `P01` of Lemma 4.1 is the case `J = J01`). -/
noncomputable def projNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (J : Finset (Fin M))
    (v : Fin n → ℝ) : ℝ :=
  ‖(colSpan X J).starProjection (WithLp.toLp 2 v)‖

end LassoDantzig.REConditions
