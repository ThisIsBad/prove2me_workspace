import Mathlib

open MeasureTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- The deterministic recursion of Eq. (7) driven by a fixed noise sequence `ξ`:
`x 0 = x₀` and `x t = x (t-1) - γ t • (R (x (t-1)) + ξ t)` for `t ≥ 1`.
The step sizes `γ t` and the noise `ξ t` are used for `t ≥ 1` only. -/
noncomputable def detIterate {N : ℕ} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → EuclideanSpace ℝ (Fin N)) : ℕ → EuclideanSpace ℝ (Fin N)
  | 0 => x₀
  | t + 1 => detIterate x₀ γ R ξ t - γ (t + 1) • (R (detIterate x₀ γ R ξ t) + ξ (t + 1))

/-- The averaged iterate `x̄_t = (1/t) ∑_{i=0}^{t-1} x_i` of Eq. (7) (equal to `0` at `t = 0`). -/
noncomputable def detAverage {N : ℕ} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → EuclideanSpace ℝ (Fin N)) (t : ℕ) : EuclideanSpace ℝ (Fin N) :=
  (t : ℝ)⁻¹ • ∑ i ∈ Finset.range t, detIterate x₀ γ R ξ i

/-- The stochastic approximation process of Eq. (7): `x_t(ω)` is the recursion `detIterate`
run along the noise path `t ↦ ξ t ω`, from the nonrandom starting point `x₀`. -/
noncomputable def saIterate {N : ℕ} {Ω : Type*} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin N) :=
  detIterate x₀ γ R (fun s => ξ s ω) t

/-- The averaged stochastic approximation estimate `x̄_t(ω) = (1/t) ∑_{i=0}^{t-1} x_i(ω)` of
Eq. (7). -/
noncomputable def saAverage {N : ℕ} {Ω : Type*} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin N) :=
  detAverage x₀ γ R (fun s => ξ s ω) t

/-- The matrix `M` acting on `ℝ^N` (Euclidean space) as a linear map, `v ↦ M v`. -/
noncomputable def matApply {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  Matrix.toEuclideanLin M v

/-- The operator norm of `M` on Euclidean `ℝ^N` (the matrix norm `‖M‖` of the Appendix). -/
noncomputable def matNorm {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- `Re λ_i(A) > 0` for every (complex) eigenvalue of `A`, i.e. `-A` is Hurwitz
(Assumption 2.1; the eigenvalue part of Assumption 3.2). -/
def EigenRePos {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), 0 < μ.re

/-- Condition (4) of Assumption 2.2 for steps indexed from `t = 1`:
`γ_t > 0` for `t ≥ 1`, `γ_t → 0`, and `(γ_t - γ_{t+1}) / γ_t = o(γ_t)`. -/
def StepCondition4 (γ : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 < γ t) ∧ Tendsto γ atTop (𝓝 0) ∧
    (fun t => (γ t - γ (t + 1)) / γ t) =o[atTop] γ

/-- The matrices `X_j^t` of (A1): `X_j^j = I` and `X_j^{t+1} = X_j^t - γ_t A X_j^t` for `t ≥ j`,
so `X_j^t = (I - γ_{t-1} A) ⋯ (I - γ_j A)` for `t ≥ j`. For `t < j` the value is `I`
(never used). -/
noncomputable def lemX {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j : ℕ) :
    ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 1
  | t + 1 => if j ≤ t then lemX A γ j t - γ t • (A * lemX A γ j t) else 1

/-- `X̄_j^t = γ_j ∑_{i=j}^{t-1} X_j^i` of (A1). -/
noncomputable def lemXbar {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  γ j • ∑ i ∈ Finset.Ico j t, lemX A γ j i

/-- `φ_j^t = A⁻¹ - X̄_j^t` (Appendix, before Lemma 1). -/
noncomputable def lemPhi {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  A⁻¹ - lemXbar A γ j t

/-- `α_j^t = γ_j ∑_{i=j}^{t-1} ∏_{k=j+1}^{i} (I - γ_k A) = γ_j ∑_{i=j}^{t-1} X_{j+1}^{i+1}`
(proof of Lemma 2, p. 847). -/
noncomputable def lemAlpha {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  γ j • ∑ i ∈ Finset.Ico j t, lemX A γ (j + 1) (i + 1)

/-- `w_j^t = α_j^t - A⁻¹` (proof of Lemma 2, p. 847). -/
noncomputable def lemW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  lemAlpha A γ j t - A⁻¹

end PolyakJuditsky.Averaging
