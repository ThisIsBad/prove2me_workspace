import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- An affine matrix-valued map given by its coefficients (El Ghaoui–Oustry–Lebret 1998, (1),
p. 33, and §5.6, p. 44): `affineMap A x = A₀ + ∑ᵢ xᵢ Aᵢ`, where the coefficient `A (i+1)` is the
paper's `A_{i+1}` multiplying the `i`-th coordinate of `x : Fin m → ℝ` (0-based). Used for
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`) and for `H(x) = H₀ + ∑ xᵢ Hᵢ` (`p × q`). -/
def affineMap {m r c : ℕ} (A : Fin (m + 1) → Matrix (Fin r) (Fin c) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin r) (Fin c) ℝ :=
  A 0 + ∑ i : Fin m, x i • A i.succ

/-- The `i`-th block `Δᵢ` (`r × c`) of a block row `Δ = [Δ₀ … Δ_m]`, stored as one
`r × (m+1)c` matrix whose columns are indexed by pairs `(i, b)`: `(block Δ i) a b = Δ a (i, b)`. -/
def block {m r c : ℕ} (Δ : Matrix (Fin r) (Fin (m + 1) × Fin c) ℝ) (i : Fin (m + 1)) :
    Matrix (Fin r) (Fin c) ℝ :=
  Matrix.of fun a b => Δ a (i, b)

/-- The unstructured perturbation of an LMI (§5.1, p. 41):
`F(x, Δ) = F(x) + Δ₀ + Δ₀ᵀ + ∑ᵢ xᵢ (Δᵢ + Δᵢᵀ)`, with `Δ = [Δ₀ … Δ_m]` a block row of `n × n`
blocks, stored as one `n × n(m+1)` matrix. -/
def perturbedLMI {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ) (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  affineMap Fs x + (block Δ 0 + (block Δ 0)ᵀ) +
    ∑ i : Fin m, x i • (block Δ i.succ + (block Δ i.succ)ᵀ)

/-- The robust feasible set (2), p. 35, of the unstructured model of §5.1 (`𝒟` the whole space
of `n × n(m+1)` matrices): `x` is robustly feasible iff `F(x, Δ) ⪰ 0` for every `Δ` whose
spectral norm (largest singular value, as one `n × n(m+1)` matrix) is at most `ρ`. There is no
inverse in this model (`D = 0`), so no well-posedness condition is needed. -/
def robustFeasibleSet {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ, ‖Δ‖ ≤ ρ → (perturbedLMI Fs Δ x).PosSemidef}

/-- The matrix `R(x) = [1; x] ⊗ I` of (19), p. 41: an `n(m+1) × n` matrix whose `i`-th `n × n`
block is `x̃ᵢ I`, where `x̃ = (1, x₁, …, x_m)`. Rows are indexed by pairs `(i, a)`. -/
def rMat {m n : ℕ} (x : Fin m → ℝ) : Matrix (Fin (m + 1) × Fin n) (Fin n) ℝ :=
  Matrix.of fun ia b => (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) ia.1 * (1 : Matrix (Fin n) (Fin n) ℝ) ia.2 b

/-- The block matrix of the LMI (20), p. 41, in the variables `(x, τ)`:
`[[F(x) − τI, [1 xᵀ] ⊗ ρI], [[1 xᵀ]ᵀ ⊗ ρI, τI]]`, i.e.
`fromBlocks (F(x) − τI) (ρ R(x)ᵀ) (ρ R(x)) (τ I)` with `R(x) = [1; x] ⊗ I` (`rMat`); the
diagonal blocks are `n × n` and `n(m+1) × n(m+1)`. -/
def lmi20 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ τ : ℝ) (x : Fin m → ℝ) :
    Matrix (Fin n ⊕ (Fin (m + 1) × Fin n)) (Fin n ⊕ (Fin (m + 1) × Fin n)) ℝ :=
  fromBlocks (affineMap Fs x - τ • (1 : Matrix (Fin n) (Fin n) ℝ)) (ρ • (rMat x)ᵀ) (ρ • rMat x)
    (τ • (1 : Matrix (Fin (m + 1) × Fin n) (Fin (m + 1) × Fin n) ℝ))

/-- The full perturbation of a norm-minimization problem (§5.6, pp. 44–45):
`H(x, Δ) = H₀ + Δ₀ + ∑ᵢ xᵢ (Hᵢ + Δᵢ)`, with `Δ = [Δ₀ … Δ_m]` a block row of `p × q` blocks,
stored as one `p × q(m+1)` matrix. -/
def perturbedH {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ)
    (Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ) (x : Fin m → ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  Hs 0 + block Δ 0 + ∑ i : Fin m, x i • (Hs i.succ + block Δ i.succ)

end RobustSDP.Unstructured
