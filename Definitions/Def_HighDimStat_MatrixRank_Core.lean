import Mathlib

namespace HighDimStat.MatrixRank

/-- The trace inner product `⟨⟨A, B⟩⟩ := trace(Aᵀ B) = Σⱼ₁ⱼ₂ Aⱼ₁ⱼ₂ Bⱼ₁ⱼ₂` on the matrix space
`ℝ^{d1×d2}` (Eq. (10.1), p. 312). -/
def traceInner {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The Frobenius norm `|||A|||_F := sqrt(Σⱼ₁ⱼ₂ (Aⱼ₁ⱼ₂)²)` induced by the trace inner product
(p. 312), the Euclidean norm on the vectorized matrix. -/
noncomputable def frobeniusNorm {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

/-- The `ℓ2`-operator (spectral) norm `|||A|||₂ := sup_{‖v‖₂=1} ‖Av‖₂` of a (possibly
rectangular) real matrix, the dual norm of the nuclear norm (Table 9.1). Realized via the
Rayleigh-type variational characterization, matching the pattern of `HighDimStat.Pca.opNormSymm`
for the symmetric case (chunk `08-pca`), generalized here to a rectangular domain/codomain. -/
noncomputable def opNorm {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  ⨆ v : {v : Fin d2 → ℝ // ∑ j, (v j) ^ 2 = 1}, Real.sqrt (∑ i, (A.mulVec v.1 i) ^ 2)

/-- The singular values of a real matrix `Θ : ℝ^{d1×d2}`, indexed by `Fin d2` and given (in
decreasing order) by the square roots of the eigenvalues of the positive semidefinite Gram
matrix `Θᵀ Θ`. Indexed through `eigenvalues₀` directly via `finCongr (Fintype.card_fin d2)`
rather than Mathlib's `Matrix.IsHermitian.eigenvalues` (which reindexes `eigenvalues₀` along
`Fintype.equivOfCardEq`, a classically-chosen bijection Mathlib proves no order relationship
for): `finCongr (Fintype.card_fin d2) : Fin (Fintype.card (Fin d2)) ≃ Fin d2` is definitionally
`Fin.cast` under the proof `Fintype.card_fin d2 : Fintype.card (Fin d2) = d2`, hence trivially
order-preserving, so the antitonicity of `eigenvalues₀`
(`Matrix.IsHermitian.eigenvalues₀_antitone`) transfers to `singularValues` by construction. When
`d2 > d1`, the indices beyond `d' := min d1 d2` carry the (correct) value zero, so any sum over a
suffix of indices agrees with the book's own sum over `j = r+1, ..., d'`. -/
noncomputable def singularValues {d1 d2 : ℕ} (Θ : Matrix (Fin d1) (Fin d2) ℝ) : Fin d2 → ℝ :=
  fun j => Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self Θ).1.eigenvalues₀
    ((finCongr (Fintype.card_fin d2)).symm j))

/-- The nuclear norm `|||Θ|||_nuc := Σⱼ σⱼ(Θ)` (Eq. (10.5), p. 313), the sum of the singular
values of `Θ`. -/
noncomputable def nuclearNorm {d1 d2 : ℕ} (Θ : Matrix (Fin d1) (Fin d2) ℝ) : ℝ :=
  ∑ j, singularValues Θ j

/-- The tail sum `Σ_{j=r+1}^{d'} σⱼ(Θ)` of singular values of `Θ` beyond the top `r`, as used
in Proposition 10.6's approximation-error term: the sum of `singularValues Θ j` over indices
`j` (0-indexed) with `r ≤ j`, i.e. the book's 1-indexed `j = r+1, ..., d'`. -/
noncomputable def tailSingularSum {d1 d2 : ℕ} (Θ : Matrix (Fin d1) (Fin d2) ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ (Finset.univ : Finset (Fin d2)).filter (fun j : Fin d2 => r ≤ (j : ℕ)), singularValues Θ j

/-- The observation operator `Xn(Θ) := (⟨⟨Xᵢ, Θ⟩⟩)ᵢ` of Eq. (10.2)-(10.3), p. 312: given the
design matrices `Xs : Fin n → ℝ^{d1×d2}`, `Xn Xs Θ` is the `n`-vector of trace-inner-product
observations. -/
def observationOp {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (Θ : Matrix (Fin d1) (Fin d2) ℝ) : Fin n → ℝ :=
  fun i => traceInner (Xs i) Θ

/-- The adjoint observation operator `X*ₙ(u) := Σᵢ uᵢXᵢ` of p. 312: the linear map from `ℝⁿ`
to `ℝ^{d1×d2}` adjoint to `observationOp`. -/
def observationOpAdjoint {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (u : Fin n → ℝ) : Matrix (Fin d1) (Fin d2) ℝ :=
  ∑ i, u i • Xs i

/-- The restricted strong convexity condition (10.17), p. 318, for the least-squares cost
under nuclear norm regularization, with curvature `κ` and tolerance parameter `c0`:
`‖Xn(Δ)‖₂²/(2n) ≥ κ/2 |||Δ|||_F² − c0(d1+d2)/n |||Δ|||_nuc²` for all `Δ`. -/
def RSCNuclear {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (κ c0 : ℝ) : Prop :=
  ∀ Δ : Matrix (Fin d1) (Fin d2) ℝ,
    (∑ i, (observationOp Xs Δ i) ^ 2) / (2 * (n : ℝ)) ≥
      κ / 2 * (frobeniusNorm Δ) ^ 2 - c0 * ((d1 : ℝ) + d2) / (n : ℝ) * (nuclearNorm Δ) ^ 2

/-- The `Φ*`-curvature condition (10.20), p. 320, with curvature `κ` and tolerance `τn`, for
the least-squares cost under nuclear norm regularization (dual norm = operator norm):
`|||(1/n) X*ₙXn(Δ)|||₂ ≥ κ|||Δ|||₂ − τn|||Δ|||_nuc` for all `Δ`. -/
def DualCurvatureNuclear {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (κ τn : ℝ) : Prop :=
  ∀ Δ : Matrix (Fin d1) (Fin d2) ℝ,
    opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs (observationOp Xs Δ)) ≥
      κ * opNorm Δ - τn * nuclearNorm Δ

/-- `Θhat` solves the nuclear-norm regularized least-squares program (10.16), p. 319:
`argmin_Θ (1/2n)‖y − Xn(Θ)‖₂² + λₙ|||Θ|||_nuc`. -/
def IsNuclearNormLSSolution {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ)
    (y : Fin n → ℝ) (lamN : ℝ) (Θhat : Matrix (Fin d1) (Fin d2) ℝ) : Prop :=
  ∀ Θ : Matrix (Fin d1) (Fin d2) ℝ,
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - observationOp Xs Θhat i) ^ 2) + lamN * nuclearNorm Θhat ≤
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - observationOp Xs Θ i) ^ 2) + lamN * nuclearNorm Θ

end HighDimStat.MatrixRank
