import Mathlib

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- Column `j` of a real `m × n` matrix, as a vector of Euclidean space `ℝ^m` (so that `‖·‖` is
the ℓ2 norm and `⟪·,·⟫_ℝ` the dot product). -/
def colE {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => A i j)

/-- The matrix whose `j`-th column is the vector `cols j`. -/
def colsMatrix {m : ℕ} {ι : Type*} (cols : ι → EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) ι ℝ :=
  Matrix.of fun i j => cols j i

/-- Normalization of a vector with respect to the ℓ2 norm, `v / ‖v‖₂`.
Lean's convention `0⁻¹ = 0` sends the zero vector to itself. -/
noncomputable def normalizeVec {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  ‖v‖⁻¹ • v

/-- The set of indices of the nonzero entries of `x`. -/
noncomputable def nzSet {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- The number of nonzero entries of `x`. -/
noncomputable def nnz {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  (nzSet x).card

/-- `Opt(δ)`: the fewest number of nonzero entries over all `x` with `‖Ax − b‖₂ ≤ δ`.
(Lean's `sInf ∅ = 0`: the value is meaningful only when such an `x` exists.) -/
noncomputable def optSparsity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (δ : ℝ) : ℕ :=
  sInf {N : ℕ | ∃ x : EuclideanSpace ℝ (Fin n),
    nnz x = N ∧ ‖Matrix.toEuclideanLin A x - b‖ ≤ δ}

/-- The bold `A` of the paper: `A` with each column normalized with respect to the ℓ2 norm
(a zero column stays zero). -/
noncomputable def Abar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  colsMatrix (fun j => normalizeVec (colE A j))

/-- `P` is the Moore–Penrose pseudo-inverse of `M`: the four Penrose equations. -/
def IsMoorePenrose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (P : Matrix κ ι ℝ) : Prop :=
  M * P * M = M ∧ P * M * P = P ∧ (M * P).transpose = M * P ∧ (P * M).transpose = P * M

/-- The spectral norm `‖P‖₂`: the operator norm of `P` from `ℓ2` to `ℓ2`. -/
noncomputable def opNorm2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P)‖

/-- `u` is a vector with the minimum number of nonzero entries among all `v` with
`‖∑ᵢ vᵢ cᵢ − c‖₂ ≤ δ`, where `cᵢ = cols i` (the paper's `u⁽ʳ⁾` for `cols = A⁽ʳ⁾`,
`c = b⁽ʳ⁾`, `δ = ε/2`). -/
def IsMinSparseSol {m n : ℕ} (cols : Fin n → EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin m)) (δ : ℝ) (u : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖(∑ i, u i • cols i) - c‖ ≤ δ ∧
    ∀ v : EuclideanSpace ℝ (Fin n), ‖(∑ i, v i • cols i) - c‖ ≤ δ → nnz u ≤ nnz v

end SparseApprox.Greedy
