import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

/-!
Megiddo, J. ACM 31 (1984), §3.1 p. 117 and §3.2 p. 118: in dimension one a single query
(at the median) settles the position of `x*` relative to at least half of `n` given
hyperplanes, i.e. `A(1) = 1`, `B(1) = 1/2`.
-/

namespace MegiddoLP.FixedDim

/-- **`A(1) = 1`, `B(1) = 1/2`.** For `n` hyperplanes `{x ∈ ℝ | aᵢ x = bᵢ}` with `aᵢ ≠ 0`
there is a strategy making at most one query which, for every unknown point `x`, reports
correct positions (`lt`/`eq`/`gt` of `aᵢ x` against `bᵢ`) for at least half of the hyperplanes
(`n ≤ 2 · #settled`). -/
theorem one_query_halves (n : ℕ) (a : Fin n → Fin 1 → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ∃ T : QTree 1 (Fin n → Option Ordering), ∀ x : Fin 1 → ℝ,
      T.numQueries x ≤ 1 ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      n ≤ 2 * (Finset.univ.filter fun i => (T.eval x i).isSome).card := by sorry

end MegiddoLP.FixedDim
