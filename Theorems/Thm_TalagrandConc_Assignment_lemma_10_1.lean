import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

namespace TalagrandConc.Assignment

/-- Talagrand (1995), p. 167, Lemma 10.1. For an `α`-expanding digraph `D`, an integer
`m ≥ 1` with `α^m ≥ N/2` and an assignment `τ`, every `i ∈ I` lies on a cycle
`i_1 = i, i_2, …, i_{n+1} = i` with `1 ≤ n ≤ 2m`, `i_1, …, i_n` pairwise distinct and
`(i_ℓ, τ(i_{ℓ+1})) ∈ D` for `1 ≤ ℓ ≤ n`. Indices are 0-based: `c ℓ` is `i_{ℓ+1}`. -/
theorem lemma_10_1 {N : ℕ} (D : Set (Fin N × Fin N)) (α : ℝ) (hD : IsExpanding N α D)
    (m : ℕ) (hm : 1 ≤ m) (hαm : (N : ℝ) / 2 ≤ α ^ m) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 * m ∧ ∃ c : ℕ → Fin N, c 0 = i ∧ c n = i ∧
      (∀ a b : ℕ, a < n → b < n → c a = c b → a = b) ∧
      ∀ ℓ : ℕ, ℓ < n → (c ℓ, τ (c (ℓ + 1))) ∈ D := by sorry

end TalagrandConc.Assignment

