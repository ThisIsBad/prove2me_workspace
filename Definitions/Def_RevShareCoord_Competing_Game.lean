import Mathlib

/-!
# The competing-retailers quantity game (Cachon–Lariviere, June 2000 working paper, Sec. 3.2)

A single supplier sells through `n` locations `i : Fin n`, each run by an independent retailer.
A stocking profile is `q : Fin n → ℝ` (the paper's `q̄ = {q₁, …, qₙ}`), and the revenue at
location `i` is `R i q` (the paper's `Rᵢ(q̄)`). The supplier offers retailer `i` a
revenue-sharing contract `(φ, wᵢ)`: retailer `i` pays `wᵢ` per unit and keeps the fraction `φ`
of its revenue. The wholesale-price contract is the case `φ = 1`.
-/

namespace RevShareCoord.Competing

open Finset

variable {n : ℕ}

/-- Retailer `i`'s profit under the revenue-sharing contract `(φ, w̄)` at the profile `q`:
`π_{rᵢ}(q̄, φ, w̄) = φ Rᵢ(q̄) − wᵢ qᵢ` (Sec. 3.2, p. 14). With `φ = 1` this is the
wholesale-price profit `π_{rᵢ}(q̄, w̄) = Rᵢ(q̄) − qᵢ wᵢ` (p. 14). -/
def retailerProfit (R : Fin n → (Fin n → ℝ) → ℝ) (φ : ℝ) (w : Fin n → ℝ)
    (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  φ * R i q - w i * q i

/-- The supplier's profit under the revenue-sharing contracts `(φ, wᵢ)`: she receives
`wᵢ qᵢ` and `(1 − φ) Rᵢ(q̄)` from every retailer and pays `c` per unit produced,
`π_s(q̄, φ, w̄) = Σᵢ ((1 − φ) Rᵢ(q̄) + wᵢ qᵢ) − c Σᵢ qᵢ` (Sec. 3.2, p. 14). With `φ = 1` this is
the wholesale-price profit `π_s(q̄, w̄) = Σᵢ (wᵢ − c) qᵢ`. -/
def supplierProfit (R : Fin n → (Fin n → ℝ) → ℝ) (c φ : ℝ) (w : Fin n → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ i, ((1 - φ) * R i q + w i * q i) - c * ∑ i, q i

/-- The integrated system profit `Π(q̄) = R(q̄) − c Σᵢ qᵢ` with `R(q̄) = Σᵢ Rᵢ(q̄)`
(Sec. 3.2, p. 12). -/
def systemProfit (R : Fin n → (Fin n → ℝ) → ℝ) (c : ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i, R i q - c * ∑ i, q i

/-- A (pure-strategy) **Nash equilibrium in order quantities** of the retailers' game under the
contracts `(φ, wᵢ)` (Sec. 3.2, pp. 13–14): every quantity is nonnegative, and no retailer `i`
gains by changing its own quantity to any `x ≥ 0` while the other retailers keep theirs. -/
def IsNashEquilibrium (R : Fin n → (Fin n → ℝ) → ℝ) (φ : ℝ) (w : Fin n → ℝ)
    (q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧
    ∀ (i : Fin n) (x : ℝ), 0 ≤ x →
      retailerProfit R φ w (Function.update q i x) i ≤ retailerProfit R φ w q i

end RevShareCoord.Competing
