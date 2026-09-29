import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- Theorem 5.6, p. 48 (§5.8, error-in-variables RSDPs). Let `F(x) = F₀ + ∑ xᵢFᵢ` with symmetric
`n × n` coefficients, and for `i = 1, …, m` write `Fᵢ = 2 LᵢRᵢ` with `Lᵢ, Rᵢᵀ ∈ ℝ^{n×rᵢ}`,
`rᵢ = rank Fᵢ`; put `L = [L₁ … L_m]`, `R = [R₁; …; R_m]` and let `𝒮` be the block-diagonal
matrices `diag(S₁, …, S_m)`, `Sᵢ ∈ ℝ^{rᵢ×rᵢ}`. If `x_feas` satisfies, for some `λ ≥ 0`,
`S = Sᵀ ∈ 𝒮` and `G = −Gᵀ ∈ 𝒮`,
`[[F(x_feas) − λI − LSLᵀ, (1/2)Rᵀ + LG], [(1/2)R − GLᵀ, S]] ≻ 0`,
then every integer vector `z` closest to `x_feas` in the maximum norm satisfies `F(z) ⪰ 0`
(is feasible for (32)). -/
theorem theorem_5_6 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (r : Fin m → ℕ)
    (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ)
    (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ)
    (hFLR : ∀ i : Fin m, Fs i.succ = (2 : ℝ) • (Ls i * Rs i))
    (hrank : ∀ i : Fin m, (Fs i.succ).rank = r i)
    (xfeas : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (Sb Gb : (i : Fin m) → Matrix (Fin (r i)) (Fin (r i)) ℝ)
    (hS : (blockDiagonal' Sb).IsSymm) (hG : (blockDiagonal' Gb)ᵀ = -blockDiagonal' Gb)
    (hLMI : (fromBlocks
      (affineMap Fs xfeas - lam • (1 : Matrix (Fin n) (Fin n) ℝ) -
        blockRow Ls * blockDiagonal' Sb * (blockRow Ls)ᵀ)
      ((1 / 2 : ℝ) • (blockCol Rs)ᵀ + blockRow Ls * blockDiagonal' Gb)
      ((1 / 2 : ℝ) • blockCol Rs - blockDiagonal' Gb * (blockRow Ls)ᵀ)
      (blockDiagonal' Sb)).PosDef) :
    ∀ z : Fin m → ℤ,
      (∀ z' : Fin m → ℤ,
        ‖(fun i => (z i : ℝ)) - xfeas‖ ≤ ‖(fun i => (z' i : ℝ)) - xfeas‖) →
      (affineMap Fs (fun i => (z i : ℝ))).PosSemidef := by sorry

end RobustSDP.Structured

