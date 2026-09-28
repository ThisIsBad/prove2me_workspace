import Mathlib

namespace ThreeOpSplitting.Convergence

/-- The three-operator map of Eq. (1.2), `T := T₁ ∘ (2T₂ - I - γ C ∘ T₂) + I - T₂`;
with `T₁ = J_{γA}` and `T₂ = J_{γB}` it is the operator `T` of Davis–Yin, and with general
`T₁, T₂` it is the operator of Proposition 2.1. -/
def threeOp {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (T₁ T₂ C : H → H) : H → H :=
  fun z => T₁ ((2 : ℝ) • T₂ z - z - γ • C (T₂ z)) + z - T₂ z

/-- The sequence `z^k` of Algorithm 1: `z^0` given and
`z^{k+1} = z^k + λ_k (x_A^k - x_B^k)` with `x_B^k = J_B z^k`,
`x_A^k = J_A (2 x_B^k - z^k - γ C x_B^k)`. -/
def zSeq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (JA JB C : H → H) (lam : ℕ → ℝ) (z0 : H) : ℕ → H
  | 0 => z0
  | k + 1 =>
    let z := zSeq γ JA JB C lam z0 k
    z + lam k • (JA ((2 : ℝ) • JB z - z - γ • C (JB z)) - JB z)

/-- The sequence `x_B^k = J_B(z^k)` of Algorithm 1 (step 1). -/
def xBSeq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (JA JB C : H → H) (lam : ℕ → ℝ) (z0 : H) (k : ℕ) : H :=
  JB (zSeq γ JA JB C lam z0 k)

/-- The sequence `x_A^k = J_A(2 x_B^k - z^k - γ C x_B^k)` of Algorithm 1 (step 2). -/
def xASeq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (JA JB C : H → H) (lam : ℕ → ℝ) (z0 : H) (k : ℕ) : H :=
  JA ((2 : ℝ) • xBSeq γ JA JB C lam z0 k - zSeq γ JA JB C lam z0 k
    - γ • C (xBSeq γ JA JB C lam z0 k))

/-- The averagedness coefficient `α = 1/(2 - ε)` of Corollary 2.1 and Theorem 2.1. -/
noncomputable def alpha (ε : ℝ) : ℝ := 1 / (2 - ε)

/-- The coefficient `τ_k = λ_k(1 - λ_k) + λ_k(1 - α)/α` (with `α = alpha ε`), as used in the
proof of Theorem 2.1 (p. 836); it equals `λ_k(1 - α λ_k)/α`. -/
noncomputable def tau (ε l : ℝ) : ℝ := l * (1 - l) + l * (1 - alpha ε) / alpha ε

end ThreeOpSplitting.Convergence
