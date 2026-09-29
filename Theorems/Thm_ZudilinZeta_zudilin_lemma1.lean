import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_lemma1 (P : Params) (n : ℕ) (hn : 0 < n) :
    (∃ c : ℕ → ℚ,
        F P n = (c 0 : ℝ)
          + ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), (c k : ℝ) * zetaR (P.r + 2 * k)) ∧
      (∃ a : ℕ → ℤ,
        Lambda P n = (a 0 : ℝ)
          + ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), (a k : ℝ) * zetaR (P.r + 2 * k)) := by
  sorry
end ZudilinZeta
