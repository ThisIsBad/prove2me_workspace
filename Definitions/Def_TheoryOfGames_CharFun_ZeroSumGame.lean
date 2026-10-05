import Mathlib

namespace TheoryOfGames.CharFun

/-- A zero-sum `n`-person game in normalized form (11.2.3, 25.1.3, (25:1)).
Players are `k : Fin n` (the book's players `1, …, n` are `0, …, n - 1` here). Player `k`
chooses `τ k : Fin (β k)`, i.e. one of `β k ≥ 1` pure strategies (the book's
`τ_k = 1, …, β_k`), each player uninformed about the others' choices. When the strategy
profile `τ = (τ₁, …, τₙ)` is played, player `k` receives `H τ k` (the book's `ℋ_k(τ₁, …, τₙ)`),
and the game is zero-sum: `∑ k, H τ k = 0` for every profile, which is (25:1). -/
structure ZeroSumGame (n : ℕ) where
  /-- `β k` is the number of pure strategies of player `k`. -/
  β : Fin n → ℕ
  /-- Every player has at least one pure strategy. -/
  β_pos : ∀ k, 0 < β k
  /-- `H τ k = ℋ_k(τ₁, …, τₙ)`, the amount player `k` gets. -/
  H : ((k : Fin n) → Fin (β k)) → Fin n → ℝ
  /-- (25:1): `∑_{k=1}^n ℋ_k(τ₁, …, τₙ) ≡ 0`. -/
  zero_sum : ∀ τ, ∑ k, H τ k = 0

end TheoryOfGames.CharFun
