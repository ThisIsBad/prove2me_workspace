import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

/-!
Megiddo, J. ACM 31 (1984), §3.1–§3.2 p. 118: for every dimension `d` there is a constant
`C = C(d)`, independent of `n`, such that `C · log n` queries suffice to determine the
position of `x*` relative to all `n` given hyperplanes in `ℝ^d`.
-/

namespace MegiddoLP.FixedDim

/-- **Multidimensional search with `C(d) log n` queries.** For `d ≥ 1` there is a constant `C`
such that for every `n ≥ 2` and all hyperplanes `{aᵢ ⬝ᵥ x = bᵢ}` (`i < n`) in `ℝ^d` with
`aᵢ ≠ 0`, some strategy determines, for every unknown point `x`, the positions of `x` relative
to all `n` hyperplanes using at most `C log n` queries (natural logarithm). -/
theorem log_queries_all (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ (a : Fin n → Fin d → ℝ) (b : Fin n → ℝ), (∀ i, a i ≠ 0) →
      ∃ T : QTree d (Fin n → Ordering), ∀ x : Fin d → ℝ,
        T.eval x = (fun i => compare (a i ⬝ᵥ x) (b i)) ∧
        (T.numQueries x : ℝ) ≤ C * Real.log n := by sorry

end MegiddoLP.FixedDim

