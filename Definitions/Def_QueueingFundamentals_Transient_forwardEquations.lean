import Mathlib

namespace QueueingFundamentals.Transient

/-- Right-hand side of the M/M/1/1 equations (2.70), for the state `p = (p₀, p₁)`:
`p₀' = -λ p₀ + μ p₁`, `p₁' = -μ p₁ + λ p₀`. -/
def mm11RHS (lam mu : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun k => if k = 0 then -lam * p 0 + mu * p 1 else -mu * p 1 + lam * p 0

/-- Right-hand side of the M/M/1 forward equations (2.72):
`p₀' = -λ p₀ + μ p₁` and `p_n' = -(λ+μ) p_n + λ p_{n-1} + μ p_{n+1}` for `n > 0`. -/
def mm1RHS (lam mu : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => -lam * p 0 + mu * p 1
  | n + 1 => -(lam + mu) * p (n + 1) + lam * p n + mu * p (n + 2)

/-- Right-hand side of the M/M/∞ forward equations (2.76), with `λ_n = λ`, `μ_n = nμ`:
`p₀' = -λ p₀ + μ p₁` and `p_n' = -(λ + nμ) p_n + λ p_{n-1} + (n+1)μ p_{n+1}` for `n > 0`. -/
def mmInfRHS (lam mu : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => -lam * p 0 + mu * p 1
  | n + 1 => -(lam + ((n : ℝ) + 1) * mu) * p (n + 1) + lam * p n + ((n : ℝ) + 2) * mu * p (n + 2)

/-- Right-hand side of the busy-period equations of §2.12 (p.102): the M/M/1 equations with an
absorbing barrier at `0` (`λ₀ = 0`): `p₀' = μ p₁`, `p₁' = -(λ+μ) p₁ + μ p₂`, and
`p_n' = -(λ+μ) p_n + λ p_{n-1} + μ p_{n+1}` for `n ≥ 2`. -/
def busyRHS (lam mu : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => mu * p 1
  | 1 => -(lam + mu) * p 1 + mu * p 2
  | n + 2 => -(lam + mu) * p (n + 2) + lam * p (n + 1) + mu * p (n + 3)

/-- `p` solves the differential–difference system with right-hand side `F` on `[0, ∞)`: for every
state `n` and every `t ≥ 0`, `p_n` has derivative `F(p(t))_n` at `t` within `[0, ∞)` (an ordinary
derivative for `t > 0`, the right derivative at `t = 0`). -/
def IsForwardSolution {S : Type*} (F : (S → ℝ) → S → ℝ) (p : S → ℝ → ℝ) : Prop :=
  ∀ n : S, ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (p n) (F (fun m => p m t) n) (Set.Ici (0 : ℝ)) t

/-- `p(t)` is a probability distribution on the states for every `t ≥ 0`:
`p_n(t) ≥ 0` and `∑_n p_n(t) = 1`. This is the class in which the transient solutions are
unique. -/
def IsProbabilityFamily {S : Type*} (p : S → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (∀ n : S, 0 ≤ p n t) ∧ HasSum (fun n => p n t) 1

end QueueingFundamentals.Transient
