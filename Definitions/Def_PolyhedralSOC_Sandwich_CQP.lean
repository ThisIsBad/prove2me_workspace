import Mathlib

open Matrix

namespace PolyhedralSOC.Sandwich

/-- The Euclidean norm `‖y‖₂ = √(yᵀy)` of a vector `y ∈ ℝ^k`
(Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), p. 193 (PDF p. 1)). Written out explicitly
because the norm Mathlib puts on `Fin k → ℝ` is the sup norm. -/
noncomputable def eucNorm {k : ℕ} (y : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, y i ^ 2)

/-- The data of a conic quadratic problem
`(CQP)  min_x {eᵀx | Ax ≥ b, ‖A_ℓ x − b_ℓ‖₂ ≤ c_ℓᵀx − d_ℓ, ℓ = 1, …, m}`
(Ben-Tal & Nemirovski 2001, p. 193 (PDF p. 1)) with `x ∈ ℝ^n`, `A` a `k₀ × n` matrix,
`b ∈ ℝ^{k₀}`, and for each of the `m` conic constraints (indexed by `Fin m`, 0-based)
a `k_ℓ × n` matrix `A_ℓ`, `b_ℓ ∈ ℝ^{k_ℓ}`, `c_ℓ ∈ ℝ^n`, `d_ℓ ∈ ℝ`. The row sizes `k_ℓ`
may differ from constraint to constraint. -/
structure CQP (n k₀ m : ℕ) where
  /-- objective vector `e` -/
  e : Fin n → ℝ
  /-- the `k₀ × n` matrix `A` of the linear constraints `Ax ≥ b` -/
  A : Matrix (Fin k₀) (Fin n) ℝ
  /-- the right-hand side `b` of the linear constraints -/
  b : Fin k₀ → ℝ
  /-- the row size `k_ℓ` of `A_ℓ` -/
  k : Fin m → ℕ
  /-- the `k_ℓ × n` matrix `A_ℓ` of the `ℓ`-th conic constraint -/
  Aℓ : (ℓ : Fin m) → Matrix (Fin (k ℓ)) (Fin n) ℝ
  /-- the vector `b_ℓ ∈ ℝ^{k_ℓ}` of the `ℓ`-th conic constraint -/
  bℓ : (ℓ : Fin m) → Fin (k ℓ) → ℝ
  /-- the vector `c_ℓ ∈ ℝ^n` of the `ℓ`-th conic constraint -/
  c : Fin m → Fin n → ℝ
  /-- the scalar `d_ℓ` of the `ℓ`-th conic constraint -/
  d : Fin m → ℝ

/-- `Feas(CQP)`: the feasible set of (CQP) (Ben-Tal & Nemirovski 2001, p. 193 (PDF p. 1)),
the points `x` with `Ax ≥ b` (componentwise) and `‖A_ℓ x − b_ℓ‖₂ ≤ c_ℓᵀx − d_ℓ` for
every `ℓ`. -/
def feas {n k₀ m : ℕ} (P : CQP n k₀ m) : Set (Fin n → ℝ) :=
  {x | (∀ i, P.b i ≤ (P.A *ᵥ x) i) ∧
    ∀ ℓ, eucNorm (P.Aℓ ℓ *ᵥ x - P.bℓ ℓ) ≤ P.c ℓ ⬝ᵥ x - P.d ℓ}

/-- `Feas(CQP_ε)`: the feasible set of the `ε`-relaxation
`(CQP_ε)  min_x {eᵀx | Ax ≥ b, ‖A_ℓ x − b_ℓ‖₂ ≤ (1+ε)[c_ℓᵀx − d_ℓ], ℓ = 1, …, m}`
(Ben-Tal & Nemirovski 2001, p. 194 (PDF p. 2)). -/
def feasRelaxed {n k₀ m : ℕ} (P : CQP n k₀ m) (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, P.b i ≤ (P.A *ᵥ x) i) ∧
    ∀ ℓ, eucNorm (P.Aℓ ℓ *ᵥ x - P.bℓ ℓ) ≤ (1 + ε) * (P.c ℓ ⬝ᵥ x - P.d ℓ)}

end PolyhedralSOC.Sandwich
