import Mathlib
import Definitions.Def_LinearOptimization_SimplexPivot

open Matrix

namespace GassSaaty.ParametricPivot

open LinearOptimization

/-- Gass–Saaty §2, Case A (p. 40) and footnote 4: the coefficient `α_j` of the linear function
`"z_j − c_j" = α_j + λβ_j` with respect to the basis `B`, i.e. `z_j − c_j` computed for the cost
vector `d`. Here `z_j = Σ_i y_ij c_{B(i)}` with `y_ij = (B⁻¹A_j)_i`, so `z_j − c_j` is the
**negative** of the Bertsimas–Tsitsiklis reduced cost `reducedCost A d B j = d_j − d_B'B⁻¹A_j`. -/
noncomputable def alpha {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) : ℝ :=
  -reducedCost A d B j

/-- Gass–Saaty §2, Case A (p. 40): the coefficient `β_j` of `λ` in `"z_j − c_j" = α_j + λβ_j`
with respect to the basis `B`, i.e. `z_j − c_j` computed for the cost vector `d'`
(negative of the reduced cost `reducedCost A d' B j`). -/
noncomputable def beta {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) : ℝ :=
  -reducedCost A d' B j

/-- Gass–Saaty Eq. (5), right half (p. 40): `λ̄ = min_{β_j > 0} (−α_j/β_j)`, and `λ̄ = +∞` if
`β_j ≤ 0` for every `j`. Valued in `WithTop ℝ`: the infimum of the empty family is `⊤ = +∞`. -/
noncomputable def lamBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) : WithTop ℝ :=
  (Finset.univ.filter fun j => 0 < beta A d' B j).inf
    fun j => ((-alpha A d B j / beta A d' B j : ℝ) : WithTop ℝ)

/-- Gass–Saaty Eq. (5), left half (p. 40): `λ̲ = max_{β_j < 0} (−α_j/β_j)`, and `λ̲ = −∞` if
`β_j ≥ 0` for every `j`. Valued in `WithBot ℝ`: the supremum of the empty family is `⊥ = −∞`. -/
noncomputable def lamLower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) : WithBot ℝ :=
  (Finset.univ.filter fun j => beta A d' B j < 0).sup
    fun j => ((-alpha A d B j / beta A d' B j : ℝ) : WithBot ℝ)

end GassSaaty.ParametricPivot
