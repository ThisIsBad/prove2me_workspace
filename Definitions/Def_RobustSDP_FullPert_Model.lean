import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- An affine matrix-valued map given by its coefficients (El Ghaoui–Oustry–Lebret 1998, (1),
p. 33, and §2.2, p. 35): `affineMap A x = A₀ + ∑ᵢ xᵢ Aᵢ`, where the coefficient `A (i+1)` is the
paper's `A_{i+1}` multiplying the `i`-th coordinate of `x : Fin m → ℝ` (0-based). Used both for
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`) and for `R(x) = R₀ + ∑ xᵢ Rᵢ` (`q × n`). -/
def affineMap {m r c : ℕ} (A : Fin (m + 1) → Matrix (Fin r) (Fin c) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin r) (Fin c) ℝ :=
  A 0 + ∑ i : Fin m, x i • A i.succ

/-- The linear-fractional representation (5), p. 35:
`F(x, Δ) = F(x) + L Δ (I − DΔ)⁻¹ R(x) + R(x)ᵀ (I − ΔᵀDᵀ)⁻¹ Δᵀ Lᵀ`, written for given values
`Fx = F(x)` (`n × n`) and `Rx = R(x)` (`q × n`), with `L : n × p`, `D : q × p`, `Δ : p × q`.
Mathlib's `⁻¹` returns `0` on a singular matrix, so this expression is only meaningful where
`det (1 - D * Δ) ≠ 0`; every use states that guard next to it. -/
noncomputable def lfr {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ) (Rx : Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (Δ : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Fx + L * Δ * (1 - D * Δ)⁻¹ * Rx + Rxᵀ * (1 - Δᵀ * Dᵀ)⁻¹ * Δᵀ * Lᵀ

/-- The robust feasible set (2), p. 35, for the perturbation model `(F(·), R(·), L, D, 𝒟, ρ)`:
`x` is robustly feasible iff for every `Δ ∈ 𝒟` with spectral norm `‖Δ‖ ≤ ρ`, `F(x, Δ)` is well
defined (`det (I − DΔ) ≠ 0`) and `F(x, Δ) ⪰ 0`. The norm is the largest singular value
(`Matrix.Norms.L2Operator`), and `⪰ 0` is `Matrix.PosSemidef` (symmetric positive semidefinite). -/
def robustFeasibleSet {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ →
    (1 - D * Δ).det ≠ 0 ∧ (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosSemidef}

/-- The `(n + q) × (n + q)` block matrix of the LMI (10), p. 36, in the variables `(x, τ)`,
written for given values `Fx = F(x)`, `Rx = R(x)`:
`[[F(x) − τLLᵀ, R(x)ᵀ − τLDᵀ], [R(x) − τDLᵀ, τ(ρ⁻²I − DDᵀ)]]`
(`Matrix.fromBlocks A B C D` has `B` top-right and `C` bottom-left). -/
noncomputable def sdpLMI {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ) (Rx : Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (ρ τ : ℝ) :
    Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ :=
  fromBlocks (Fx - τ • (L * Lᵀ)) (Rxᵀ - τ • (L * Dᵀ)) (Rx - τ • (D * Lᵀ))
    (τ • ((ρ ^ 2)⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ) - D * Dᵀ))

end RobustSDP.FullPert
