import Mathlib

open Matrix

namespace LimitedBFGS.SQN

/-- `ρ = 1 / yᵀs` (Nocedal 1980, p. 774, below (3); p. 775, `ρ_i = 1/y_iᵀs_i`).
If `yᵀs = 0` then Lean's `1 / 0 = 0` gives `ρ = 0`. -/
noncomputable def bfgsRho {n : ℕ} (s y : Fin n → ℝ) : ℝ :=
  1 / (y ⬝ᵥ s)

/-- `v = I − ρ y sᵀ` (Nocedal 1980, p. 775, `v_i = (I − ρ_i y_i s_iᵀ)`). -/
noncomputable def bfgsV {n : ℕ} (s y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - bfgsRho s y • vecMulVec y s

/-- The BFGS update of `H` by the pair `(s, y)` in product form (3), p. 774:
`H̄ = (I − ρ s yᵀ) H (I − ρ y sᵀ) + ρ s sᵀ = vᵀ H v + ρ s sᵀ`.
When `yᵀs = 0`, `ρ = 0` and `v = I`, so the step returns `H` unchanged: this is the paper's
"dropping a correction is equivalent to defining `v = I` and `ρssᵀ = 0`" (p. 774). -/
noncomputable def bfgsStep {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (bfgsV s y)ᵀ * H * bfgsV s y + bfgsRho s y • vecMulVec s s

/-- The BFGS correction `U(s, y, H)` of the sum form (1)–(2), p. 774:
`U(s, y, H) = (s sᵀ / yᵀs) [yᵀHy / yᵀs + 1] − (1 / yᵀs) [s yᵀ H + H y sᵀ]`,
so that the BFGS update is `H̄ = H + U(s, y, H)`. -/
noncomputable def bfgsU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (((y ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ s) + 1) / (y ⬝ᵥ s)) • vecMulVec s s
    - (1 / (y ⬝ᵥ s)) • (vecMulVec s y * H + H * vecMulVec y s)

end LimitedBFGS.SQN
