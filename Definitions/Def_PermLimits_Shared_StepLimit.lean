import Mathlib

/-!
# The limit permutation `Z_σ` of a permutation

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 11, Definition 3.4, Eqs. (25)–(26).
-/

namespace PermLimits.Shared

open unitInterval

/-- **The limit permutation `Z_σ`** (Hoppen et al., arXiv:1103.5844v2, Definition 3.4,
Eqs. (25)–(26), p. 11). For `σ ∈ S_n`, `(X_σ, Y_σ)` has density
`f_σ(x, y) = n · 1[σ(⌈n x⌉) = ⌈n y⌉]` and `Z_σ(x, y) = ∫₀^y f_σ(x, ỹ) dỹ`.

**Formalization Note.** The integral (26) is written in closed form. With 0-based indices
(`σ : Equiv.Perm (Fin n)`), a point `x ∈ ((i-1)/n, i/n]` lies in row `i - 1 = ⌈n x⌉ - 1` and
`Z_σ(x, y) = min(1, max(0, n y - j))` with `j = σ(⌈n x⌉ - 1)` (as a natural number): the uniform
cdf on `[j/n, (j+1)/n]`. At `x = 0`, where `⌈n x⌉ = 0` and the paper's density refers to the
undefined `σ(0)`, the natural-number subtraction gives row `0`, so `Z_σ(0, ·)` is the cdf of row
`0`; this changes `Z_σ` only on the null set `{x = 0}` and makes `Z_σ(x, ·)` a cdf for every `x`,
as Definition 1.3(a) requires. The argument is named `π` because `σ` is reserved notation once
`unitInterval` is opened. The `min … (n - 1)` never changes the index for `x ∈ [0, 1]`
(`⌈n x⌉ ≤ n`); it only certifies the bound `< n`. For the empty permutation (`n = 0`, not a
permutation in the paper, which has `n ≥ 1`) the uniform limit permutation `Z_u(x, y) = y` is
returned. -/
noncomputable def stepLimit {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : I) : ℝ :=
  if h : 0 < n then
    min 1 (max 0 ((n : ℝ) * (y : ℝ) -
      ((π ⟨min (⌈(n : ℝ) * (x : ℝ)⌉₊ - 1) (n - 1), by omega⟩ : Fin n) : ℕ)))
  else (y : ℝ)

end PermLimits.Shared
