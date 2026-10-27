import Mathlib

namespace CongestedPlatforms.Surge

/-- Case P balanced demand (4.3): `d^P_i(p_i) = λ (αp_i − c)(1 − p_i)/(αp_i − c + λγ)`. -/
noncomputable def dP (lam γ α c p : ℝ) : ℝ :=
  lam * (α * p - c) * (1 - p) / (α * p - c + lam * γ)

/-- Case F balanced demand (4.4) of the platform charging `pi` against a rival charging `pj`. -/
noncomputable def dF (lam γ α c pi pj : ℝ) : ℝ :=
  lam * (α * pi - c) * (lam * γ + (α * pj - c) * (1 - pi + pj)) /
    (2 * (α * pi - c) * (α * pj - c) + lam * γ * (α * (pi + pj) - 2 * c))

/-- Case P balanced supply (4.6): `s^P_i(p_i) = (αp_i − c) √(λ(1 − p_i)/(αp_i − c + λγ))`. -/
noncomputable def sP (lam γ α c p : ℝ) : ℝ :=
  (α * p - c) * Real.sqrt (lam * (1 - p) / (α * p - c + lam * γ))

/-- Case F balanced supply (4.7) of the platform charging `pi` against a rival charging `pj`. -/
noncomputable def sF (lam γ α c pi pj : ℝ) : ℝ :=
  (α * pi - c) * Real.sqrt (lam * (lam * γ + (α * pj - c) * (1 - pi + pj)) /
    (2 * (α * pi - c) * (α * pj - c) + lam * γ * (α * (pi + pj) - 2 * c)))

/-- Balanced demand (4.2) of the platform charging `pi` against a rival charging `pj`:
Case P when `d^P(p_i) + d^P(p_j) ≤ λ`, Case F otherwise. -/
noncomputable def D (lam γ α c pi pj : ℝ) : ℝ :=
  if dP lam γ α c pi + dP lam γ α c pj ≤ lam then dP lam γ α c pi else dF lam γ α c pi pj

/-- Balanced supply (4.5), with the same case switch as (4.2). -/
noncomputable def S (lam γ α c pi pj : ℝ) : ℝ :=
  if dP lam γ α c pi + dP lam γ α c pj ≤ lam then sP lam γ α c pi else sF lam γ α c pi pj

/-- Platform profit `Π_i(p_i, p_j) = [(1 − α)p_i + c] min{D_i, S_i}` (p. 14). -/
noncomputable def profit (lam γ α c pi pj : ℝ) : ℝ :=
  ((1 - α) * pi + c) * min (D lam γ α c pi pj) (S lam γ α c pi pj)

/-- The supply constraint (3.6): `D_i(p_i, p_j) ≤ S_i(p_i, p_j)`. -/
def SupplyOK (lam γ α c pi pj : ℝ) : Prop :=
  D lam γ α c pi pj ≤ S lam γ α c pi pj

/-- `(p, p)` is a symmetric Nash equilibrium of the pricing game (p. 14) on the action set
`[p̲, p̄] = [c/α, 1]`: `p` satisfies (3.6), and no price `q ∈ [c/α, 1]` satisfying (3.6) against
`p` earns a higher profit. -/
def IsSymNE (lam γ α c p : ℝ) : Prop :=
  c / α ≤ p ∧ p ≤ 1 ∧ SupplyOK lam γ α c p p ∧
    ∀ q : ℝ, c / α ≤ q → q ≤ 1 → SupplyOK lam γ α c q p →
      profit lam γ α c q p ≤ profit lam γ α c p p

/-- Utilization `ρ = D/S` when both platforms charge `p` and the market size is `lam`. -/
noncomputable def rho (lam γ α c p : ℝ) : ℝ :=
  D lam γ α c p p / S lam γ α c p p

/-- Utility (3.1a) of a customer at location `v` using platform 0, both platforms charging `p`,
market size `lam`. -/
noncomputable def uD0 (lam γ α c v p : ℝ) : ℝ :=
  1 - v - p - γ * (rho lam γ α c p) ^ 2

/-- Utility (3.1b) of a customer at location `v` using platform 1, both platforms charging `p`,
market size `lam`. -/
noncomputable def uD1 (lam γ α c v p : ℝ) : ℝ :=
  v - p - γ * (rho lam γ α c p) ^ 2

/-- Utility (3.4) of a driver with operating cost `k`, both platforms charging `p`,
market size `lam`. -/
noncomputable def uS (lam γ α c k p : ℝ) : ℝ :=
  -k + (α * p - c) * rho lam γ α c p

/-- Region (a) of Proposition 1 (p. 16), as printed. -/
def RegionA (lam γ c : ℝ) : Prop :=
  (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∧ lam * (1 - c) / (1 + 2 * lam) ≤ γ

/-- Region (d) of Proposition 1 (p. 16), as printed. -/
def RegionD (lam γ c : ℝ) : Prop :=
  γ < (1 / 2 - c) ^ 2 / (2 * lam) ∧ lam / 2 ≤ γ

end CongestedPlatforms.Surge
