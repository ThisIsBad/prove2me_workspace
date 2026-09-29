import Mathlib

open Matrix

namespace RobustSDP.Uniqueness

/-- The data of the robust SDP (15) of El Ghaoui–Oustry–Lebret (1998), §4, p. 38, in the case of
full perturbations with `D = 0` and `ρ = 1`: the coefficients of the affine maps
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`, Eq. (1), p. 33) and `R(x) = R₀ + ∑ xᵢ Rᵢ` (`q × n`, §2.2, p. 35),
and the matrix `L` (`n × p`). The coefficient `Fs i` (resp. `Rs i`), `i : Fin m`, is the paper's
`F_{i+1}` (resp. `R_{i+1}`), multiplying the 0-based coordinate `x i`. -/
structure SDPData (m n p q : ℕ) where
  /-- `F₀` -/
  F0 : Matrix (Fin n) (Fin n) ℝ
  /-- `F₁, …, F_m` -/
  Fs : Fin m → Matrix (Fin n) (Fin n) ℝ
  /-- `L ∈ ℝ^{n×p}` -/
  L : Matrix (Fin n) (Fin p) ℝ
  /-- `R₀` -/
  R0 : Matrix (Fin q) (Fin n) ℝ
  /-- `R₁, …, R_m` -/
  Rs : Fin m → Matrix (Fin q) (Fin n) ℝ

namespace SDPData

variable {m n p q : ℕ} (D : SDPData m n p q)

/-- `F(x) = F₀ + ∑ᵢ xᵢ Fᵢ` (Eq. (1), p. 33). -/
def F (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D.F0 + ∑ i, x i • D.Fs i

/-- `R(x) = R₀ + ∑ᵢ xᵢ Rᵢ` (§2.2, p. 35). -/
def R (x : Fin m → ℝ) : Matrix (Fin q) (Fin n) ℝ :=
  D.R0 + ∑ i, x i • D.Rs i

/-- The homogenized pencil `λ R₀ + ∑ᵢ xᵢ Rᵢ` of hypothesis H3(a) (p. 38). -/
def pencil (lam : ℝ) (x : Fin m → ℝ) : Matrix (Fin q) (Fin n) ℝ :=
  lam • D.R0 + ∑ i, x i • D.Rs i

/-- The constraint matrix of the SDP (15) (p. 38),
`𝓕(x, τ) = [[F(x) − τLLᵀ, R(x)ᵀ], [R(x), τI]]`, an `(n+q) × (n+q)` block matrix. -/
def lmi (x : Fin m → ℝ) (τ : ℝ) : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ :=
  fromBlocks (D.F x - τ • (D.L * D.Lᵀ)) (D.R x)ᵀ (D.R x) (τ • (1 : Matrix (Fin q) (Fin q) ℝ))

/-- A point `y = (x, τ)` is feasible for the SDP (15): `𝓕(x, τ) ⪰ 0`. -/
def Feasible (y : (Fin m → ℝ) × ℝ) : Prop :=
  (D.lmi y.1 y.2).PosSemidef

/-- `y = (x, τ)` is optimal for (15) with objective `cᵀx`: it is feasible, and `cᵀx ≤ cᵀx'` for
every feasible `(x', τ')`. -/
def IsOptimal (c : Fin m → ℝ) (y : (Fin m → ℝ) × ℝ) : Prop :=
  D.Feasible y ∧ ∀ y' : (Fin m → ℝ) × ℝ, D.Feasible y' → c ⬝ᵥ y.1 ≤ c ⬝ᵥ y'.1

/-- The matrix `G(y) = F(x) − τLLᵀ − (1/τ) R(x)ᵀR(x)` of §4.2 (p. 39), for `y = (x, τ)`.
Only meaningful for `τ ≠ 0` (Lean's `τ⁻¹` is `0` at `τ = 0`). -/
noncomputable def G (y : (Fin m → ℝ) × ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D.F y.1 - y.2 • (D.L * D.Lᵀ) - y.2⁻¹ • ((D.R y.1)ᵀ * D.R y.1)

end SDPData

end RobustSDP.Uniqueness
