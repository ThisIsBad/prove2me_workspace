import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_model
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized

namespace NonuniformCompetitive.Snoopy

/-- Theorem 4, first claim (Karlin et al. 1994, p. 551): in the single-block snoopy-caching
task system with `n ≥ 2` processors and block-transfer cost `p ≥ 1`, no randomized on-line
algorithm is competitive against an oblivious adversary within a factor less than
`e_p / (e_p − 1)`: from every initial state `s₀`, if `A` is `c`-competitive from `s₀` on
admissible request sequences, then `c ≥ e_p / (e_p − 1)`. -/
theorem no_better_ratio (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n)
    (A : RandomizedAlgorithm n p) (c : ℝ) (hA : A.IsCompetitiveFrom s₀ c) :
    ep p / (ep p - 1) ≤ c := by sorry

end NonuniformCompetitive.Snoopy

