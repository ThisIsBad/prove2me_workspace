import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting

namespace RobustUncLP.Ellipsoidal

open Matrix

open EllipsoidalData

variable {m n k : ℕ}

/-- Feasible set of the problem `(P_i[x])`, Appendix, p. 15: tuples `(u⁰, …, u^k)` with
`Π_ℓ(u^ℓ) = Π_0(u⁰)` and `‖Q_ℓ u^ℓ‖ ≤ 1` for all `ℓ` (it depends neither on `i` nor on `x`). -/
def PFeas (D : EllipsoidalData m n k) : Set ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ) :=
  {u | (∀ ℓ, D.Pi ℓ (u ℓ) = D.Pi 0 (u 0)) ∧ ∀ ℓ, euclidNorm (D.Q ℓ *ᵥ u ℓ) ≤ 1}

/-- Frobenius pairing `⟨X, Y⟩ = ∑_{a,b} X_{ab} Y_{ab}` of two `m × n` matrices. -/
def frob (X Y : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, X a b * Y a b

/-- The system `(𝒞_i)`, Appendix, p. 16, for row `i` at the point `x`, written out for the data of
`(P_i[x])`. `Λ ℓ'` is the multiplier `λ^{(i)}` of the equality `Π_{ℓ'+1}(u^{ℓ'+1}) = Π_0(u⁰)`,
`μ ℓ`, `ν ℓ` are `μ_ℓ^{(i)}`, `ν_ℓ^{(i)}` (`ℓ = 0, …, k`). -/
def SystemC (D : EllipsoidalData m n k) (x : Fin n → ℝ) (i : Fin m)
    (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ) (μ : (ℓ : Fin (k + 1)) → Fin (D.M ℓ) → ℝ)
    (ν : Fin (k + 1) → ℝ) : Prop :=
  -- first line of (𝒞_i): the dual objective is nonnegative
  0 ≤ (D.P0 0 *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P0 0 - D.P0 ℓ'.succ) - ∑ ℓ, ν ℓ ∧
  -- second line, `u⁰`-block
  (∀ j, -(∑ ℓ' : Fin k, frob (Λ ℓ') (D.P 0 j)) + ((D.Q 0)ᵀ *ᵥ μ 0) j = (D.P 0 j *ᵥ x) i) ∧
  -- second line, `u^ℓ`-blocks, `ℓ = 1, …, k`
  (∀ ℓ' : Fin k, ∀ j, frob (Λ ℓ') (D.P ℓ'.succ j) + ((D.Q ℓ'.succ)ᵀ *ᵥ μ ℓ'.succ) j = 0) ∧
  -- third line
  ∀ ℓ, euclidNorm (μ ℓ) ≤ ν ℓ

end RobustUncLP.Ellipsoidal
