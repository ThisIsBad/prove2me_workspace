import Mathlib

namespace TheoryOfGames.GeneralGames

/-- A general `n`-person game in normalized form (11.2.3, 56.2.2): no zero-sum condition.
Players are `k : Fin n` (the book's players `1, …, n` are `0, …, n - 1` here). Player `k`
chooses `τ k : Fin (β k)`, one of `β k ≥ 1` pure strategies (the book's `τ_k = 1, …, β_k`),
each player uninformed about the others' choices. When the profile `τ = (τ₁, …, τₙ)` is
played, player `k` receives `H τ k` (the book's `ℋ_k(τ₁, …, τₙ)`), an arbitrary real number. -/
structure GeneralGame (n : ℕ) where
  /-- `β k` is the number of pure strategies of player `k`. -/
  β : Fin n → ℕ
  /-- Every player has at least one pure strategy. -/
  β_pos : ∀ k, 0 < β k
  /-- `H τ k = ℋ_k(τ₁, …, τₙ)`, the amount player `k` gets. -/
  H : ((k : Fin n) → Fin (β k)) → Fin n → ℝ

/-- A general game is *zero-sum* (25:1) if `∑_{k=1}^n ℋ_k(τ₁, …, τₙ) ≡ 0`: the zero-sum
`n`-person games of Chapter VI are exactly the general games with this property. -/
def GeneralGame.IsZeroSum {n : ℕ} (Γ : GeneralGame n) : Prop :=
  ∀ τ, ∑ k, Γ.H τ k = 0

end TheoryOfGames.GeneralGames
