import Mathlib

namespace LawlerMoore.WeightedTardy

/-- The function `f(j, t)` of Equation (3) (Lawler–Moore 1969, §6, p. 80), as printed:
for the paper's job `j ≥ 1` (Lean job `⟨j - 1, _⟩`) and `0 ≤ t`,
`f(j, t) = max{f(j, t - 1), f(j - 1, t), p_j + f(j - 1, t - a'_j)}` if `t ≤ d_j`, and
`f(j, t) = f(j, d_j)` if `t > d_j`.
The base cases, not printed with (3), are those of Equation (1) (p. 77) with `+∞` replaced by
`-∞` for a maximum: `f(0, t) = 0` for `t ≥ 0` and `f(j, t) = -∞` (`⊥`) for `t < 0`.
For `j > n` (no such job) the value is `f(j - 1, t)`; this case is never used. -/
noncomputable def eq3 {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) : ℕ → ℤ → WithBot ℝ
  | 0, t => if 0 ≤ t then 0 else ⊥
  | j + 1, t =>
    if ht : t < 0 then ⊥
    else if h : j < n then
      if htd : t ≤ (d ⟨j, h⟩ : ℤ) then
        max (max (eq3 a' d p (j + 1) (t - 1)) (eq3 a' d p j t))
          ((p ⟨j, h⟩ : WithBot ℝ) + eq3 a' d p j (t - (a' ⟨j, h⟩ : ℤ)))
      else eq3 a' d p (j + 1) (d ⟨j, h⟩ : ℤ)
    else eq3 a' d p j t
termination_by j t => (j, (t + 1).toNat)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact Prod.Lex.right _ (by omega)

end LawlerMoore.WeightedTardy
