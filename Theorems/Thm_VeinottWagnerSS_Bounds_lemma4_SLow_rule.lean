import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Lemma 4, p. 548, in the form its proof establishes. Let `Y` (the paper's `Yⁿ`) be an optimal
policy for the `n`-period model (`n ≥ 2`) that uses the `(s_n, S_n)` rule in period 1, with
`s_n ≤ s̄` (the reduction "by lemma 3 we may assume that `s_n ≤ s̄`" of the paper's proof; without
it `(s_n, S̲)` need not be an `(s, S)` rule). If `S̄ < S_n`, then there is an admissible policy
`Y'` that uses the `(s_n, S̲)` rule in period 1 and satisfies `f_n(x | Y') ≤ f_n(x | Y)` for all
`x`. -/
theorem lemma4_SLow_rule (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) (hs : sn ≤ sHigh G K α) (hlt : SHigh G K α < Sn) :
    ∃ Y' : Policy, Admissible Y' ∧ UsesRule Y' 0 sn (SLow G) ∧
      ∀ x : ℤ, cost φ G K α n x Y' ≤ cost φ G K α n x Y := by sorry

end VeinottWagnerSS.Bounds

