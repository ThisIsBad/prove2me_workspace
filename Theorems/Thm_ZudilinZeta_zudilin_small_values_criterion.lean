import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_small_values_criterion (P : Params) (hr : P.r = 3)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ Lambda P n ≠ 0 ∧ |Lambda P n| < ε) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by sorry
end ZudilinZeta
