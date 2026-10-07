import Mathlib

namespace LawlerMoore.FunctionalEq

/-- The function `f(j, t)` of Eq. (1) (Lawler and Moore 1969, p. 77), with values in
`WithTop ℝ` (`⊤` is the paper's `+∞`, and `↑x + ⊤ = ⊤`):

* `f(j, t) = +∞` for `t < 0`;
* `f(0, t) = 0` for `t ≥ 0`;
* `f(j, t) = min {f(j, t − 1), α_j(t) + f(j − 1, t − a_j), β_j(t) + f(j − 1, t − b_j)}`
  for `j = 1, …, n` and `t ≥ 0`.

The paper's job `j` is Lean job `⟨j - 1, _⟩`, so `f (j + 1)` uses `α ⟨j, _⟩`, `a ⟨j, _⟩`.
Losses are evaluated at `t.toNat`, which equals `t` under the guard `0 ≤ t`. For `j > n` the
paper does not define `f`; here `f j t = ⊤` there, a value never used. The recursion is
well founded on `(j, (t + 1).toNat)` lexicographically. -/
def f {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) : ℕ → ℤ → WithTop ℝ
  | j, t =>
    if _ht : t < 0 then ⊤
    else
      match j with
      | 0 => 0
      | j + 1 =>
        if hj : j < n then
          min (f a b α β (j + 1) (t - 1))
            (min ((α ⟨j, hj⟩ t.toNat : WithTop ℝ) + f a b α β j (t - (a ⟨j, hj⟩ : ℤ)))
              ((β ⟨j, hj⟩ t.toNat : WithTop ℝ) + f a b α β j (t - (b ⟨j, hj⟩ : ℤ))))
        else ⊤
termination_by j t => (j, (t + 1).toNat)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; omega)

end LawlerMoore.FunctionalEq
