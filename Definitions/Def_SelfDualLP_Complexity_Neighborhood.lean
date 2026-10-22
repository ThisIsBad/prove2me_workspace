import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- `d ∈ Q`: the direction `d = (d_y, d_x, d_τ, d_θ, d_s, d_κ)` lies in the null space of the
constraint matrix of (HLP) after adding the surplus variables `s` and `κ`
(Theorem 5 (ii), p. 59):
`A d_x − b d_τ + b̄ d_θ = 0`, `−Aᵀd_y + c d_τ − c̄ d_θ − d_s = 0`,
`bᵀd_y − cᵀd_x + z̄ d_θ − d_κ = 0`, `−b̄ᵀd_y + c̄ᵀd_x − z̄ d_τ = 0`,
with `b̄, c̄, z̄` built from `(x⁰, y⁰, s⁰)` by (5). -/
def InQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (d : HLPPoint m n) : Prop :=
  A *ᵥ d.x - d.τ • b + d.θ • bbar A b x0 = 0 ∧
  -(Aᵀ *ᵥ d.y) + d.τ • c - d.θ • cbar A c y0 s0 - d.s = 0 ∧
  b ⬝ᵥ d.y - c ⬝ᵥ d.x + zbar b c x0 y0 * d.θ - d.κ = 0 ∧
  -(bbar A b x0 ⬝ᵥ d.y) + cbar A c y0 s0 ⬝ᵥ d.x - zbar b c x0 y0 * d.τ = 0

/-- `Q` under the choice (7) `y⁰ = 0, x⁰ = s⁰ = e`. -/
def InQ7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : HLPPoint m n) : Prop :=
  InQ A b c (ones n) 0 (ones n) d

/-- The complementarity gap `xᵀs + τκ`. -/
def gap {m n : ℕ} (z : HLPPoint m n) : ℝ :=
  z.x ⬝ᵥ z.s + z.τ * z.κ

/-- `μ = (xᵀs + τκ)/(n + 1)`. -/
noncomputable def mu {m n : ℕ} (z : HLPPoint m n) : ℝ :=
  gap z / ((n : ℝ) + 1)

/-- `‖(Xs; τκ) − μe‖`, the Euclidean (ℓ₂) norm in `ℝ^{n+1}` of the deviation of the vector
`(x₁s₁, …, xₙsₙ, τκ)` from `μ e`. -/
noncomputable def centralityDeviation {m n : ℕ} (z : HLPPoint m n) : ℝ :=
  Real.sqrt ((∑ j, (z.x j * z.s j - mu z) ^ 2) + (z.τ * z.κ - mu z) ^ 2)

/-- The neighborhood `𝒩(β) = {z ∈ 𝓕_h° : ‖(Xs; τκ) − μe‖ ≤ βμ}` of the central path of (HLP)
under (7) (p. 60). -/
def Nbhd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ)
    (z : HLPPoint m n) : Prop :=
  HLPStrictlyFeasible7 A b c z ∧ centralityDeviation z ≤ β * mu z

/-! Generic `n̂`-vector quantities used in (14) (p. 61). -/

/-- `μ̂ = x̂ᵀŝ / n̂` for `x̂, ŝ ∈ ℝ^{n̂}`. -/
noncomputable def muHat {N : ℕ} (x s : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ s / (N : ℝ)

/-- `‖X̂ŝ − μ̂e‖`, the Euclidean norm of `(x̂ⱼŝⱼ − μ̂)ⱼ`. -/
noncomputable def deviationHat {N : ℕ} (x s : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ j, (x j * s j - muHat x s) ^ 2)

end SelfDualLP.Complexity
